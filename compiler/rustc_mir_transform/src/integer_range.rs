//! Range analysis finds lower and upper bounds to the values that variables can assume. Currently
//! only operates on integer types.

// NOTE: can implement array bounds checking elimination, overflow check elimination, static branch prediction
// TODO: remove Integer from the name

// TODO: remove
#![allow(
    dead_code,
    unused_imports,
    unused_variables,
    unreachable_code,
    unused_mut,
    unreachable_pub
)]

use std::assert_matches::assert_matches;
use std::cell::RefCell;
use std::fmt::Formatter;

use rustc_abi::{BackendRepr, FIRST_VARIANT, FieldIdx, Size, VariantIdx};
use rustc_const_eval::const_eval::{DummyMachine, throw_machine_stop_str};
use rustc_const_eval::interpret::{
    ImmTy, Immediate, InterpCx, OpTy, PlaceTy, Projectable, interp_ok,
};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_middle::bug;
use rustc_middle::mir::interpret::{InterpResult, Scalar};
use rustc_middle::mir::visit::{MutVisitor, PlaceContext, Visitor};
use rustc_middle::mir::*;
use rustc_middle::ty::{self, ScalarInt, Ty, TyCtxt};
use rustc_mir_dataflow::fmt::DebugWithContext;
use rustc_mir_dataflow::lattice::{FlatSet, HasBottom, HasTop};
use rustc_mir_dataflow::value_analysis::{
    Map, PlaceIndex, State, TrackElem, ValueOrPlace, debug_with_context,
};
use rustc_mir_dataflow::{Analysis, JoinSemiLattice, ResultsVisitor, visit_reachable_results};
use rustc_span::DUMMY_SP;
use tracing::{debug, debug_span, instrument};

use crate::patch::MirPatch;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Range {
    pub lo: ScalarInt,
    pub hi: ScalarInt,
    /// Whether the value is of a signed integer type.
    pub signed: bool,
}

impl Range {
    pub fn new(lo: ScalarInt, hi: ScalarInt, signed: bool) -> Self {
        Self { lo, hi, signed }
    }

    pub fn singleton(v: ScalarInt, signed: bool) -> Self {
        Range { lo: v, hi: v, signed }
    }

    fn compare(&self, a: ScalarInt, b: ScalarInt) -> std::cmp::Ordering {
        let size = a.size();
        if self.signed {
            a.to_int(size).cmp(&b.to_int(size))
        } else {
            a.to_uint(size).cmp(&b.to_uint(size))
        }
    }

    pub fn join(&self, other: &Self) -> Self {
        if self.signed != other.signed {
            bug!(
                "Cannot join ranges with different signedness: self.signed={}, other.signed={}",
                self.signed,
                other.signed
            );
        }

        let lo = if self.compare(self.lo, other.lo).is_le() { self.lo } else { other.lo };
        let hi = if self.compare(self.hi, other.hi).is_ge() { self.hi } else { other.hi };
        Range { lo, hi, signed: self.signed }
    }

    pub fn intersect(self, other: Self) -> Option<Self> {
        if self.signed != other.signed {
            bug!(
                "Cannot intersect ranges with different signedness: self.signed={}, other.signed={}",
                self.signed,
                other.signed
            );
        }

        let lo = if self.compare(self.lo, other.lo).is_ge() { self.lo } else { other.lo };
        let hi = if self.compare(self.hi, other.hi).is_le() { self.hi } else { other.hi };
        if self.compare(lo, hi).is_le() {
            Some(Range { lo, hi, signed: self.signed })
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeLattice {
    Bottom,
    Range(Range),
    Top,
}

impl JoinSemiLattice for RangeLattice {
    fn join(&mut self, other: &Self) -> bool {
        match (&*self, other) {
            (Self::Top, _) | (_, Self::Bottom) => false,
            (Self::Bottom, Self::Range(x)) => {
                *self = Self::Range(x.clone());
                true
            }
            (Self::Bottom, Self::Top) => {
                *self = Self::Top;
                true
            }
            (Self::Range(a), Self::Range(b)) if a == b => false,
            (Self::Range(a), Self::Range(b)) if a != b => {
                *self = Self::Range(a.join(b));
                true
            }
            (Self::Range(x), _) => false,
        }
    }
}

impl HasBottom for RangeLattice {
    const BOTTOM: Self = Self::Bottom;

    fn is_bottom(&self) -> bool {
        matches!(self, Self::Bottom)
    }
}

impl HasTop for RangeLattice {
    const TOP: Self = Self::Top;
}

pub(super) struct IntegerRange;

impl<'tcx> crate::MirPass<'tcx> for IntegerRange {
    fn is_enabled(&self, sess: &rustc_session::Session) -> bool {
        // TODO: change back to 3
        sess.mir_opt_level() >= 4
    }

    /// Returns `true` if this pass can be overridden by `-Zenable-mir-passes`
    fn can_be_overridden(&self) -> bool {
        // TODO: change later
        false
    }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) {
        let place_limit = None;
        let map = Map::new(tcx, body, place_limit);

        let results = debug_span!("analyze").in_scope(|| {
            IntegerRangeAnalysis::new(tcx, body, map).iterate_to_fixpoint(tcx, body, None)
        });

        // let mut map = const_.analysis.map;
        // dbg!(&map);

        //let mut states = const_.entry_states;
        //dbg!(&states);

        // Perform dead code elimination based on range analysis
        let patch = {
            let mut visitor = Collector::new(tcx, body, &results);
            debug_span!("collect").in_scope(|| {
                visit_reachable_results(body, &results, &mut visitor);
            });
            visitor.patch
        };

        debug_span!("patch").in_scope(|| {
            patch.apply(body);
        });
    }

    /// If this is `false`, `#[optimize(none)]` will disable the pass.
    fn is_required(&self) -> bool {
        // TODO: change later
        true
    }
}

struct IntegerRangeAnalysis<'a, 'tcx> {
    map: Map<'tcx>,
    tcx: TyCtxt<'tcx>,
    local_decls: &'a LocalDecls<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
}

impl<'tcx> Analysis<'tcx> for IntegerRangeAnalysis<'_, 'tcx> {
    type Domain = State<RangeLattice>;

    const NAME: &'static str = "IntegerRangeAnalysis";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        State::Unreachable
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        // The initial state maps all tracked places of argument projections to ⊤ and the rest to ⊥.
        assert_matches!(state, State::Unreachable);
        *state = State::new_reachable();
        for arg in body.args_iter() {
            state.flood(PlaceRef { local: arg, projection: &[] }, &self.map);
        }
    }

    fn apply_primary_statement_effect(
        &self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        _location: Location,
    ) {
        if state.is_reachable() {
            self.handle_statement(statement, state);
        }
    }

    fn apply_primary_terminator_effect<'mir>(
        &self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        _location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        if state.is_reachable() {
            self.handle_terminator(terminator, state)
        } else {
            TerminatorEdges::None
        }
    }

    fn apply_call_return_effect(
        &self,
        state: &mut Self::Domain,
        _block: BasicBlock,
        return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        if state.is_reachable() {
            self.handle_call_return(return_places, state)
        }
    }
}

impl<'a, 'tcx> IntegerRangeAnalysis<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, map: Map<'tcx>) -> Self {
        let typing_env = body.typing_env(tcx);
        Self { map, tcx, local_decls: &body.local_decls, typing_env }
    }

    fn handle_statement(&self, statement: &Statement<'tcx>, state: &mut State<RangeLattice>) {
        match &statement.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                self.handle_assign(*place, rvalue, state);
            }
            StatementKind::SetDiscriminant { box place, variant_index } => {
                self.handle_set_discriminant(*place, *variant_index, state);
            }
            StatementKind::Intrinsic(box intrinsic) => {
                self.handle_intrinsic(intrinsic);
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                // StorageLive leaves the local in an uninitialized state
                // StorageDead makes it UB to access the local afterwards
                state.flood_with(Place::from(*local).as_ref(), &self.map, RangeLattice::BOTTOM);
            }
            StatementKind::Retag(..) => {
                // We don't track references.
            }
            StatementKind::ConstEvalCounter
            | StatementKind::Nop
            | StatementKind::FakeRead(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::Coverage(..)
            | StatementKind::BackwardIncompatibleDropHint { .. }
            | StatementKind::AscribeUserType(..) => {}
        }
    }

    fn handle_intrinsic(&self, intrinsic: &NonDivergingIntrinsic<'tcx>) {
        match intrinsic {
            NonDivergingIntrinsic::Assume(..) => {
                // Could use this, but ignoring it is sound.
            }
            NonDivergingIntrinsic::CopyNonOverlapping(CopyNonOverlapping {
                dst: _,
                src: _,
                count: _,
            }) => {
                // This statement represents `*dst = *src`, `count` times.
            }
        }
    }

    fn handle_assign(
        &self,
        target: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        state: &mut State<RangeLattice>,
    ) {
        match rvalue {
            Rvalue::Use(operand) => {
                state.flood(target.as_ref(), &self.map);
                if let Some(target_idx) = self.map.find(target.as_ref()) {
                    self.assign_operand(state, target_idx, operand);
                }
            }

            Rvalue::CopyForDeref(_) => bug!("`CopyForDeref` in runtime MIR"),

            Rvalue::Aggregate(..) => {
                // todo!();
            }

            Rvalue::BinaryOp(op, box (left, right)) if op.is_overflowing() => {
                // todo!();
            }

            Rvalue::Cast(
                CastKind::PointerCoercion(ty::adjustment::PointerCoercion::Unsize, _),
                operand,
                _,
            ) => {
                // todo!()
            }
            _ => {
                let result = self.handle_rvalue(rvalue, state);
                state.assign(target.as_ref(), result, &self.map);
            }
        }
    }

    fn handle_rvalue(
        &self,
        rvalue: &Rvalue<'tcx>,
        state: &mut State<RangeLattice>,
    ) -> ValueOrPlace<RangeLattice> {
        let val = match rvalue {
            Rvalue::Cast(CastKind::IntToInt | CastKind::IntToFloat, operand, ty) => {
                // TODO:
                RangeLattice::Top
            }

            Rvalue::Cast(CastKind::FloatToInt | CastKind::FloatToFloat, operand_, ty_) => {
                RangeLattice::Top
            }

            Rvalue::Cast(CastKind::Transmute | CastKind::Subtype, operand, ty) => {
                // TODO: need to handle wrap_immediate
                self.eval_operand(operand, state)
            }

            Rvalue::BinaryOp(op, box (left, right)) if !op.is_overflowing() => {
                // Overflows must be ignored here.
                // The overflowing operators are handled in `handle_assign`.
                let (val, _overflow) = self.binary_op(state, *op, left, right);
                val
            }

            Rvalue::UnaryOp(_, operand) => {
                // TODO:
                self.eval_operand(operand, state)
            }

            Rvalue::NullaryOp(NullOp::RuntimeChecks(_)) => {
                return ValueOrPlace::TOP;
            }

            Rvalue::Discriminant(place) => {
                RangeLattice::Top
                // state.get_discr(place.as_ref(), &self.map)
            }

            Rvalue::Use(operand) => return self.handle_operand(operand, state),

            Rvalue::CopyForDeref(_) => bug!("`CopyForDeref` in runtime MIR"),

            Rvalue::ShallowInitBox(..) => bug!("`ShallowInitBox` in runtime MIR"),

            Rvalue::Ref(..) | Rvalue::RawPtr(..) => {
                // We do not track pointer ranges in this analysis.
                return ValueOrPlace::TOP;
            }
            Rvalue::Repeat(..)
            | Rvalue::ThreadLocalRef(..)
            | Rvalue::Cast(..)
            | Rvalue::BinaryOp(..)
            | Rvalue::Aggregate(..)
            | Rvalue::WrapUnsafeBinder(..) => {
                // No modification is possible through these r-values.
                return ValueOrPlace::TOP;
            }
        };
        ValueOrPlace::Value(val)
    }

    fn handle_operand(
        &self,
        operand: &Operand<'tcx>,
        state: &mut State<RangeLattice>,
    ) -> ValueOrPlace<RangeLattice> {
        match operand {
            Operand::Constant(box constant) => {
                ValueOrPlace::Value(self.handle_constant(constant, state))
            }
            Operand::Copy(place) | Operand::Move(place) => {
                // On move, we would ideally flood the place with bottom. But with the current
                // framework this is not possible (similar to `InterpCx::eval_operand`).
                self.map.find(place.as_ref()).map(ValueOrPlace::Place).unwrap_or(ValueOrPlace::TOP)
            }
        }
    }

    fn handle_terminator<'mir>(
        &self,
        terminator: &'mir Terminator<'tcx>,
        state: &mut State<RangeLattice>,
    ) -> TerminatorEdges<'mir, 'tcx> {
        match &terminator.kind {
            TerminatorKind::Call { .. } | TerminatorKind::InlineAsm { .. } => {
                // Return handled in `handle_call_return`.
            }
            TerminatorKind::Drop { place, .. } => {
                state.flood_with(place.as_ref(), &self.map, RangeLattice::BOTTOM);
            }
            TerminatorKind::Yield { .. } => {
                // They would have an effect, but are not allowed in this phase.
                bug!("encountered disallowed terminator");
            }
            TerminatorKind::SwitchInt { .. }
            | TerminatorKind::TailCall { .. }
            | TerminatorKind::Goto { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Assert { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. } => {
                // These terminators have no effect on the analysis.
                // TODO: check if that is true
            }
        }
        terminator.edges()
    }

    fn handle_call_return(
        &self,
        return_places: CallReturnPlaces<'_, 'tcx>,
        state: &mut State<RangeLattice>,
    ) {
        // TODO: not interprocedural yet
        return_places.for_each(|place| {
            state.flood(place.as_ref(), &self.map);
        })
    }

    fn handle_constant(
        &self,
        constant: &ConstOperand<'tcx>,
        _state: &mut State<RangeLattice>,
    ) -> RangeLattice {
        let ty = constant.const_.ty();
        if !ty.is_integral() {
            return RangeLattice::Top;
        }
        let signed = ty.is_signed();
        match constant.const_.try_eval_scalar_int(self.tcx, self.typing_env) {
            Some(scalar_int) => RangeLattice::Range(Range::singleton(scalar_int, signed)),
            None => RangeLattice::Top,
        }
    }

    /// Returns val and overflow
    fn binary_op(
        &self,
        state: &mut State<RangeLattice>,
        op: BinOp,
        left: &Operand<'tcx>,
        right: &Operand<'tcx>,
    ) -> (RangeLattice, RangeLattice) {
        let llat = self.eval_operand(left, state);
        let rlat = self.eval_operand(right, state);
        match (llat, rlat) {
            // Both sides are known, do the actual computation.
            (RangeLattice::Range(l), RangeLattice::Range(r)) => {
                let ty = left.ty(self.local_decls, self.tcx);
                if !ty.is_integral() {
                    return (RangeLattice::Top, RangeLattice::Top);
                }
                let Ok(layout) = self.tcx.layout_of(self.typing_env.as_query_input(ty)) else {
                    return (RangeLattice::Top, RangeLattice::Top);
                };
                let size = layout.size;
                let signed = ty.is_signed();

                use BinOp::*;
                let res = match op {
                    // TODO: handle division
                    Add | Sub | Mul => self.arith_interval(op, l, r, size, signed),
                    BitAnd | BitOr | BitXor => self.bitwise_interval(op, l, r, size),
                    // TODO: handle ShrUnchecked, ShlUnchecked
                    Shl | Shr => self.shift_interval(op, l, r, size, signed),
                    Eq | Ne | Lt | Le | Gt | Ge => self.bool_interval(op, l, r, size, signed),
                    _ => return (RangeLattice::Top, RangeLattice::Top),
                };

                (res, res)
            }
            (RangeLattice::Bottom, _)
            | (_, RangeLattice::Bottom)
            | (RangeLattice::Range(_), _)
            | (_, RangeLattice::Range(_))
            | (RangeLattice::Top, RangeLattice::Top) => {
                (RangeLattice::Bottom, RangeLattice::Bottom)
            }
        }
    }

    fn arith_interval(
        &self,
        op: BinOp,
        l: Range,
        r: Range,
        size: Size,
        signed: bool,
    ) -> RangeLattice {
        use std::cmp::{max, min};

        use BinOp::*;

        if signed {
            let to_i = |s: ScalarInt| -> i128 { s.to_int(size) };
            let ll = to_i(l.lo);
            let lh = to_i(l.hi);
            let rl = to_i(r.lo);
            let rh = to_i(r.hi);

            let (min_v, max_v) = match op {
                Add => (ll + rl, lh + rh),
                Sub => (ll - rh, lh - rl),
                Mul => {
                    let candidates = [ll * rl, ll * rh, lh * rl, lh * rh];
                    let &mn = candidates.iter().min().unwrap();
                    let &mx = candidates.iter().max().unwrap();
                    (mn, mx)
                }
                _ => unreachable!(),
            };

            RangeLattice::Range(Range::new(ScalarInt::from(min_v), ScalarInt::from(max_v), signed))
        } else {
            let to_u = |s: ScalarInt| -> u128 { s.to_uint(size) };
            let unsigned_max = size.unsigned_int_max();

            let ll = to_u(l.lo);
            let lh = to_u(l.hi);
            let rl = to_u(r.lo);
            let rh = to_u(r.hi);

            // NOTE: saturating is nightly
            let (min_v, max_v) = match op {
                Add => {
                    let min_val = ll.saturating_add(rl);
                    let max_val = std::cmp::min(lh.saturating_add(rh), unsigned_max);
                    (min_val, max_val)
                }
                Sub => {
                    let min_val = ll.saturating_sub(rh);
                    let max_val = std::cmp::min(lh.saturating_sub(rl), unsigned_max);
                    (min_val, max_val)
                }
                Mul => {
                    let candidates = [
                        ll.saturating_mul(rl),
                        ll.saturating_mul(rh),
                        lh.saturating_mul(rl),
                        lh.saturating_mul(rh),
                    ];
                    let mn = *candidates.iter().min().unwrap();
                    let max_candidate = *candidates.iter().max().unwrap();
                    let mx = std::cmp::min(max_candidate, unsigned_max);
                    (mn, mx)
                }
                _ => unreachable!(),
            };

            let res_lo = ScalarInt::try_from_uint(min_v, size)
                .unwrap_or_else(|| ScalarInt::try_from_uint(unsigned_max, size).unwrap());
            let res_hi = ScalarInt::try_from_uint(max_v, size)
                .unwrap_or_else(|| ScalarInt::try_from_uint(unsigned_max, size).unwrap());
            RangeLattice::Range(Range::new(res_lo, res_hi, signed))
        }
    }

    fn bitwise_interval(&self, op: BinOp, l: Range, r: Range, size: Size) -> RangeLattice {
        use std::cmp::{max, min};

        use BinOp::*;

        let signed = l.signed;
        let to_u = |s: ScalarInt| -> u128 { s.to_uint(size) };
        let from_u = |v: u128| -> ScalarInt {
            let truncated = size.truncate(v);
            ScalarInt::try_from_uint(truncated, size).unwrap()
        };

        match op {
            BitAnd => {
                if l.lo == l.hi && r.lo == r.hi {
                    let res = from_u(to_u(l.lo) & to_u(r.lo));
                    return RangeLattice::Range(Range::singleton(res, signed));
                }

                if !signed {
                    // 0 <= (a & b) <= min(a, b)
                    let l_hi = to_u(l.hi);
                    let r_hi = to_u(r.hi);
                    let hi = from_u(l_hi.min(r_hi));
                    let lo = from_u(0);
                    RangeLattice::Range(Range::new(lo, hi, signed))
                } else {
                    // TODO: might be able to optimize
                    RangeLattice::Top
                }
            }

            BitOr => {
                if l.lo == l.hi && r.lo == r.hi {
                    let res = from_u(to_u(l.lo) | to_u(r.lo));
                    return RangeLattice::Range(Range::singleton(res, signed));
                }

                if !signed {
                    // min >= max(lo_l, lo_r)
                    // max <= hi_l | hi_r.
                    let l_lo = to_u(l.lo);
                    let r_lo = to_u(r.lo);
                    let l_hi = to_u(l.hi);
                    let r_hi = to_u(r.hi);

                    let lo = from_u(l_lo.max(r_lo));
                    let hi = from_u(l_hi | r_hi);

                    RangeLattice::Range(Range::new(lo, hi, signed))
                } else {
                    // TODO: might be able to optimize
                    RangeLattice::Top
                }
            }

            BitXor => {
                if l.lo == l.hi && r.lo == r.hi {
                    let res = from_u(to_u(l.lo) ^ to_u(r.lo));
                    return RangeLattice::Range(Range::singleton(res, signed));
                }

                if !signed {
                    let mask = size.truncate(u128::MAX);
                    let lo = from_u(0);
                    let hi = from_u(mask);
                    RangeLattice::Range(Range::new(lo, hi, signed))
                } else {
                    // TODO: might be able to optimize
                    RangeLattice::Top
                }
            }
            _ => unreachable!(),
        }
    }

    fn shift_interval(
        &self,
        op: BinOp,
        l: Range,
        r: Range,
        size: Size,
        signed: bool,
    ) -> RangeLattice {
        use BinOp::*;

        if signed {
            // TODO: check this
            bug!("Shift on signed integers not supported");
        }

        let to_i = |s: ScalarInt| -> i128 { s.to_int(size) };
        let ll = to_i(l.lo);
        let lh = to_i(l.hi);
        let rl = to_i(r.lo);
        let rh = to_i(r.hi);

        match op {
            Shr => {
                // TODO: check these intervals
                RangeLattice::Range(Range::new(
                    ScalarInt::from(ll >> rh),
                    ScalarInt::from(lh >> rl),
                    signed,
                ))
            }
            Shl => RangeLattice::Range(Range::new(
                ScalarInt::from(ll << rl),
                ScalarInt::from(lh << rh),
                signed,
            )),
            _ => unreachable!(),
        }
    }

    fn bool_interval(
        &self,
        op: BinOp,
        l: Range,
        r: Range,
        size: Size,
        signed: bool,
    ) -> RangeLattice {
        use BinOp::*;

        let make_bool_range =
            |always_true: bool, always_false: bool, _this: &IntegerRangeAnalysis<'_, '_>| {
                let signed = false;
                if always_true && !always_false {
                    RangeLattice::Range(Range::singleton(ScalarInt::TRUE, signed))
                } else if always_false && !always_true {
                    RangeLattice::Range(Range::singleton(ScalarInt::FALSE, signed))
                } else {
                    RangeLattice::Range(Range::new(ScalarInt::FALSE, ScalarInt::TRUE, signed))
                }
            };

        // TODO: more elegan way to handle signedness?
        let (always_true, always_false) = if signed {
            let to_i = |s: ScalarInt| -> i128 { s.to_int(size) };
            let ll = to_i(l.lo);
            let lh = to_i(l.hi);
            let rl = to_i(r.lo);
            let rh = to_i(r.hi);

            match op {
                Eq => {
                    let disjoint = lh < rl || rh < ll;
                    let singleton_equal = ll == lh && rl == rh && ll == rl;
                    (singleton_equal, disjoint)
                }
                Ne => {
                    let disjoint = lh < rl || rh < ll;
                    let singleton_equal = ll == lh && rl == rh && ll == rl;
                    (disjoint, singleton_equal)
                }
                Lt => {
                    let always_true = lh < rl;
                    let always_false = ll >= rh;
                    (always_true, always_false)
                }
                Le => {
                    let always_true = lh <= rl;
                    let always_false = ll > rh;
                    (always_true, always_false)
                }
                Gt => {
                    let always_true = rh < ll;
                    let always_false = rl >= lh;
                    (always_true, always_false)
                }
                Ge => {
                    let always_true = rh <= ll;
                    let always_false = rl > lh;
                    (always_true, always_false)
                }
                _ => unreachable!(),
            }
        } else {
            let to_u = |s: ScalarInt| -> u128 { s.to_uint(size) };
            let ll = to_u(l.lo);
            let lh = to_u(l.hi);
            let rl = to_u(r.lo);
            let rh = to_u(r.hi);

            match op {
                Eq => {
                    let disjoint = lh < rl || rh < ll;
                    let singleton_equal = ll == lh && rl == rh && ll == rl;
                    (singleton_equal, disjoint)
                }
                Ne => {
                    let disjoint = lh < rl || rh < ll;
                    let singleton_equal = ll == lh && rl == rh && ll == rl;
                    (disjoint, singleton_equal)
                }
                Lt => {
                    let always_true = lh < rl;
                    let always_false = ll >= rh;
                    (always_true, always_false)
                }
                Le => {
                    let always_true = lh <= rl;
                    let always_false = ll > rh;
                    (always_true, always_false)
                }
                Gt => {
                    let always_true = rh < ll;
                    let always_false = rl >= lh;
                    (always_true, always_false)
                }
                Ge => {
                    let always_true = rh <= ll;
                    let always_false = rl > lh;
                    (always_true, always_false)
                }
                _ => unreachable!(),
            }
        };

        make_bool_range(always_true, always_false, self)
    }

    /// The caller must have flooded `place`.
    fn assign_operand(
        &self,
        state: &mut State<RangeLattice>,
        place: PlaceIndex,
        operand: &Operand<'tcx>,
    ) {
        match operand {
            Operand::Copy(rhs) | Operand::Move(rhs) => {
                if let Some(rhs_idx) = self.map.find(rhs.as_ref()) {
                    state.insert_place_idx(place, rhs_idx, &self.map);
                } else {
                    // Untracked place => Top.
                    state.insert_value_idx(place, RangeLattice::Top, &self.map);
                }
            }
            Operand::Constant(box constant) => {
                // Direct constant assignment.
                let val = self.handle_constant(constant, state);
                state.insert_value_idx(place, val, &self.map);
            }
        }
    }

    /// The caller must have flooded `place`.
    fn assign_constant(
        &self,
        state: &mut State<RangeLattice>,
        place: PlaceIndex,
        mut operand: OpTy<'tcx>,
        projection: &[PlaceElem<'tcx>],
    ) {
        todo!();
    }

    fn eval_operand(&self, op: &Operand<'tcx>, state: &mut State<RangeLattice>) -> RangeLattice {
        let value = match self.handle_operand(op, state) {
            ValueOrPlace::Value(value) => value,
            ValueOrPlace::Place(place) => state.get_idx(place, &self.map),
        };
        value
    }

    fn handle_set_discriminant(
        &self,
        place: Place<'tcx>,
        variant_index: VariantIdx,
        state: &mut State<RangeLattice>,
    ) {
        todo!();
    }

    fn eval_discriminant(&self, enum_ty: Ty<'tcx>, variant_index: VariantIdx) -> Option<Scalar> {
        todo!();
    }

    fn wrap_immediate(&self, imm: Immediate) -> RangeLattice {
        match imm {
            Immediate::Scalar(Scalar::Int(v)) => {
                // FIXME:
                // Default to unsigned if we don't have type information
                // This is used in contexts where type info might not be available
                RangeLattice::Range(Range::singleton(v, false))
            }
            Immediate::Uninit => RangeLattice::Bottom,
            _ => RangeLattice::Top,
        }
    }
}

/// This is used to visualize the dataflow analysis.
impl<'tcx> DebugWithContext<IntegerRangeAnalysis<'_, 'tcx>> for State<RangeLattice> {
    fn fmt_with(
        &self,
        ctxt: &IntegerRangeAnalysis<'_, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            State::Reachable(values) => debug_with_context(values, None, &ctxt.map, f),
            State::Unreachable => write!(f, "unreachable"),
        }
    }

    fn fmt_diff_with(
        &self,
        old: &Self,
        ctxt: &IntegerRangeAnalysis<'_, 'tcx>,
        f: &mut Formatter<'_>,
    ) -> std::fmt::Result {
        match (self, old) {
            (State::Reachable(this), State::Reachable(old)) => {
                debug_with_context(this, Some(old), &ctxt.map, f)
            }
            _ => Ok(()),
        }
    }
}

/// Helper methods for dead code elimination
impl<'a, 'tcx> IntegerRangeAnalysis<'a, 'tcx> {
    /// Evaluates a boolean operand.
    /// Returns Some(true) if always true, Some(false) if always false, None if unknown.
    fn eval_bool(&self, operand: &Operand<'tcx>, state: &State<RangeLattice>) -> Option<bool> {
        if !state.is_reachable() {
            return None;
        }

        let ty = operand.ty(self.local_decls, self.tcx);
        if !ty.is_bool() {
            return None;
        }

        let mut state_mut = state.clone();
        let value = self.eval_operand(operand, &mut state_mut);
        match value {
            RangeLattice::Bottom => None,
            RangeLattice::Top => None,
            RangeLattice::Range(Range { lo, hi, .. }) => {
                let lo_bits = lo.to_bits_unchecked();
                let hi_bits = hi.to_bits_unchecked();
                assert!(lo_bits == 0 || lo_bits == 1);
                assert!(hi_bits == 0 || hi_bits == 1);

                if lo == hi {
                    if lo_bits == 0 {
                        return Some(false);
                    } else if lo_bits == 1 {
                        return Some(true);
                    }
                }
                None
            }
        }
    }
}

struct Collector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    analysis: &'a IntegerRangeAnalysis<'a, 'tcx>,
    patch: MirPatch<'tcx>,
}

impl<'a, 'tcx> Collector<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        body: &'a Body<'tcx>,
        results: &'a rustc_mir_dataflow::Results<'tcx, IntegerRangeAnalysis<'a, 'tcx>>,
    ) -> Self {
        Self { tcx, body, analysis: &results.analysis, patch: MirPatch::new(body) }
    }
}

impl<'a, 'tcx> ResultsVisitor<'tcx, IntegerRangeAnalysis<'a, 'tcx>> for Collector<'a, 'tcx> {
    fn visit_after_primary_terminator_effect(
        &mut self,
        _analysis: &IntegerRangeAnalysis<'a, 'tcx>,
        state: &State<RangeLattice>,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        match &terminator.kind {
            TerminatorKind::Assert { cond, expected, target, unwind, msg } => {
                // Try to evaluate the condition using range analysis
                let cond_value = self.analysis.eval_bool(cond, state);

                if let Some(always_true) = cond_value {
                    // Assert always succeeds, replace with goto
                    if always_true == *expected {
                        self.patch.patch_terminator(
                            location.block,
                            TerminatorKind::Goto { target: *target },
                        );
                    } else {
                        // Assert always fails, replace with unreachable
                        self.patch.patch_terminator(location.block, TerminatorKind::Unreachable);
                    }
                }
            }

            TerminatorKind::SwitchInt { discr, targets } => {
                // First, check if we can evaluate the discriminant to a singleton range
                let mut state_mut = state.clone();
                let value = self.analysis.eval_operand(discr, &mut state_mut);

                if let RangeLattice::Range(Range { lo, hi, .. }) = value {
                    if lo == hi {
                        let bits = lo.to_bits_unchecked();
                        let target = targets.target_for_value(bits);
                        self.patch
                            .patch_terminator(location.block, TerminatorKind::Goto { target });
                        return;
                    }

                    // Filter out unreachable targets based on range
                    let lo_bits = lo.to_bits_unchecked();
                    let hi_bits = hi.to_bits_unchecked();

                    let filtered: Vec<_> = targets
                        .iter()
                        .filter(|(value, _)| *value >= lo_bits && *value <= hi_bits)
                        .collect();

                    let original_count = targets.iter().count();
                    let num_explicit_targets = filtered.len();

                    // If only one target is possible, simplify to goto
                    if num_explicit_targets == 0 {
                        let otherwise = targets.otherwise();
                        self.patch.patch_terminator(
                            location.block,
                            TerminatorKind::Goto { target: otherwise },
                        );
                    } else if num_explicit_targets < original_count {
                        // Multiple targets, but some were filtered
                        let otherwise = targets.otherwise();
                        let filtered_targets = SwitchTargets::new(filtered.into_iter(), otherwise);
                        self.patch.patch_terminator(
                            location.block,
                            TerminatorKind::SwitchInt {
                                discr: discr.clone(),
                                targets: filtered_targets,
                            },
                        );
                    }
                } else if matches!(value, RangeLattice::Bottom) {
                    self.patch.patch_terminator(location.block, TerminatorKind::Unreachable);
                }
            }
            _ => {}
        }
    }
}

// TODO: test bool interval and shift interval
#[cfg(test)]
mod tests {
    use std::num::NonZero;

    use rustc_abi::Size;

    use super::*;

    fn make_scalar_int(value: u128, size_bytes: u8) -> ScalarInt {
        let size = Size::from_bytes(size_bytes);
        ScalarInt::try_from_uint(value, size).unwrap()
    }

    fn make_signed_scalar_int(value: i128, size_bytes: u8) -> ScalarInt {
        let size = Size::from_bytes(size_bytes);
        ScalarInt::try_from_int(value, size).unwrap()
    }

    #[test]
    fn test_range_singleton() {
        let val = make_scalar_int(5, 4);
        let range = Range::singleton(val, false);
        assert_eq!(range.lo, val);
        assert_eq!(range.hi, val);
        assert!(!range.signed);
    }

    #[test]
    fn test_range_new() {
        let lo = make_scalar_int(1, 4);
        let hi = make_scalar_int(10, 4);
        let range = Range::new(lo, hi, false);
        assert_eq!(range.lo, lo);
        assert_eq!(range.hi, hi);
        assert!(!range.signed);
    }

    #[test]
    fn test_range_join_unsigned() {
        let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
        let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), false);
        let joined = r1.join(&r2);
        assert_eq!(joined.lo, make_scalar_int(1, 4));
        assert_eq!(joined.hi, make_scalar_int(10, 4));
        assert!(!joined.signed);
    }

    #[test]
    fn test_range_join_signed() {
        // [-10, -5] join [-3, 5] should be [-10, 5]
        let r1_lo = make_signed_scalar_int(-10, 4);
        let r1_hi = make_signed_scalar_int(-5, 4);
        let r1 = Range::new(r1_lo, r1_hi, true);

        let r2_lo = make_signed_scalar_int(-3, 4);
        let r2_hi = make_signed_scalar_int(5, 4);
        let r2 = Range::new(r2_lo, r2_hi, true);

        let joined = r1.join(&r2);
        assert_eq!(joined.lo.to_int(Size::from_bytes(4)), -10);
        assert_eq!(joined.hi.to_int(Size::from_bytes(4)), 5);
        assert!(joined.signed);
    }

    #[test]
    fn test_range_join_signed_negative() {
        // [-5, -1] join [-10, -3] should be [-10, -1]
        let r1 = Range::new(make_signed_scalar_int(-5, 4), make_signed_scalar_int(-1, 4), true);
        let r2 = Range::new(make_signed_scalar_int(-10, 4), make_signed_scalar_int(-3, 4), true);
        let joined = r1.join(&r2);
        assert_eq!(joined.lo.to_int(Size::from_bytes(4)), -10);
        assert_eq!(joined.hi.to_int(Size::from_bytes(4)), -1);
    }

    #[test]
    fn test_range_intersect_unsigned() {
        let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
        let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), false);
        let intersected = r1.intersect(r2).unwrap();
        assert_eq!(intersected.lo, make_scalar_int(3, 4));
        assert_eq!(intersected.hi, make_scalar_int(5, 4));
    }

    #[test]
    fn test_range_intersect_disjoint() {
        let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
        let r2 = Range::new(make_scalar_int(10, 4), make_scalar_int(20, 4), false);
        assert!(r1.intersect(r2).is_none());
    }

    #[test]
    fn test_range_intersect_signed() {
        // [-10, -5] intersect [-7, -3] should be [-7, -5]
        let r1 = Range::new(make_signed_scalar_int(-10, 4), make_signed_scalar_int(-5, 4), true);
        let r2 = Range::new(make_signed_scalar_int(-7, 4), make_signed_scalar_int(-3, 4), true);
        let intersected = r1.intersect(r2).unwrap();
        assert_eq!(intersected.lo.to_int(Size::from_bytes(4)), -7);
        assert_eq!(intersected.hi.to_int(Size::from_bytes(4)), -5);
    }

    #[test]
    fn test_range_intersect_signed_negative_positive() {
        // [-5, 5] intersect [0, 10] should be [0, 5]
        let r1 = Range::new(make_signed_scalar_int(-5, 4), make_signed_scalar_int(5, 4), true);
        let r2 = Range::new(make_signed_scalar_int(0, 4), make_signed_scalar_int(10, 4), true);
        let intersected = r1.intersect(r2).unwrap();
        assert_eq!(intersected.lo.to_int(Size::from_bytes(4)), 0);
        assert_eq!(intersected.hi.to_int(Size::from_bytes(4)), 5);
    }

    #[test]
    fn test_range_lattice_join() {
        let mut r1 =
            RangeLattice::Range(Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false));
        let r2 =
            RangeLattice::Range(Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), false));
        let changed = r1.join(&r2);
        assert!(changed);
        match r1 {
            RangeLattice::Range(r) => {
                assert_eq!(r.lo, make_scalar_int(1, 4));
                assert_eq!(r.hi, make_scalar_int(10, 4));
            }
            _ => panic!("Expected Range"),
        }
    }

    #[test]
    fn test_range_lattice_join_bottom() {
        let mut r1 = RangeLattice::Bottom;
        let r2 =
            RangeLattice::Range(Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false));
        let changed = r1.join(&r2);
        assert!(changed);
        assert!(matches!(r1, RangeLattice::Range(_)));
    }

    #[test]
    fn test_range_lattice_join_top() {
        let mut r1 = RangeLattice::Top;
        let r2 =
            RangeLattice::Range(Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false));
        let changed = r1.join(&r2);
        assert!(!changed); // Top join anything = Top (no change)
        assert!(matches!(r1, RangeLattice::Top));
    }

    #[test]
    fn test_range_lattice_join_identical() {
        let range = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
        let mut r1 = RangeLattice::Range(range);
        let r2 = RangeLattice::Range(range);
        let changed = r1.join(&r2);
        assert!(!changed); // Joining identical ranges shouldn't change
    }

    #[test]
    fn test_range_compare_unsigned() {
        let range = Range::new(make_scalar_int(1, 4), make_scalar_int(10, 4), false);
        let a = make_scalar_int(5, 4);
        let b = make_scalar_int(3, 4);
        assert!(range.compare(a, b).is_gt());
    }

    #[test]
    fn test_range_compare_signed_negative() {
        // Test that -5 < -3 for signed integers
        let range = Range::new(make_signed_scalar_int(-10, 4), make_signed_scalar_int(10, 4), true);
        let a = make_signed_scalar_int(-5, 4);
        let b = make_signed_scalar_int(-3, 4);
        assert!(range.compare(a, b).is_lt());
    }

    #[test]
    fn test_range_compare_signed_vs_unsigned() {
        // Test that signed comparison differs from unsigned for negative numbers
        // In unsigned: 0xFFFFFFFB (u32 representation of -5) > 0xFFFFFFFD (u32 representation of -3)
        // In signed: -5 < -3
        let signed_range =
            Range::new(make_signed_scalar_int(-10, 4), make_signed_scalar_int(10, 4), true);
        let unsigned_range =
            Range::new(make_scalar_int(0xFFFFFFFB, 4), make_scalar_int(0xFFFFFFFD, 4), false);

        let a = make_signed_scalar_int(-5, 4);
        let b = make_signed_scalar_int(-3, 4);

        // Signed comparison: -5 < -3
        assert!(signed_range.compare(a, b).is_lt());
        let a_unsigned = make_scalar_int(0xFFFFFFFB, 4); // -5 as u32
        let b_unsigned = make_scalar_int(0xFFFFFFFD, 4); // -3 as u32
        // As unsigned, 0xFF...FB < 0xFF...FD
        assert!(unsigned_range.compare(a_unsigned, b_unsigned).is_lt());
    }

    #[test]
    fn test_range_large_values() {
        // Test that ranges work correctly for large values that would overflow u8
        let large_val = make_scalar_int(1000, 4);
        let range = Range::singleton(large_val, false);
        assert_eq!(range.lo, large_val);
        assert_eq!(range.hi, large_val);
    }

    #[test]
    fn test_range_different_sizes() {
        let u8_val = make_scalar_int(255, 1);
        let u16_val = make_scalar_int(1000, 2);
        let u32_val = make_scalar_int(100000, 4);

        let r1 = Range::singleton(u8_val, false);
        let r2 = Range::singleton(u16_val, false);
        let r3 = Range::singleton(u32_val, false);

        assert_eq!(r1.lo.size().bytes(), 1);
        assert_eq!(r2.lo.size().bytes(), 2);
        assert_eq!(r3.lo.size().bytes(), 4);
    }

    #[test]
    fn test_range_join_preserves_signedness() {
        let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), true);
        let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), true);
        let joined = r1.join(&r2);
        assert!(joined.signed);
    }

    #[test]
    #[should_panic]
    fn test_range_join_different_signedness_panics() {
        let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
        let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), true);
        let _joined = r1.join(&r2); // Should panic with bug!()
    }

    #[test]
    #[should_panic]
    fn test_range_intersect_different_signedness_panics() {
        let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
        let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(10, 4), true);
        let _intersected = r1.intersect(r2); // Should panic with bug!()
    }

    #[test]
    fn test_range_intersect_touching() {
        // [1, 5] intersect [5, 10] should be [5, 5] (singleton)
        let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
        let r2 = Range::new(make_scalar_int(5, 4), make_scalar_int(10, 4), false);
        let intersected = r1.intersect(r2).unwrap();
        assert_eq!(intersected.lo, intersected.hi);
        assert_eq!(intersected.lo, make_scalar_int(5, 4));
    }

    #[test]
    fn test_range_join_overlapping() {
        // [1, 10] join [5, 15] should be [1, 15]
        let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(10, 4), false);
        let r2 = Range::new(make_scalar_int(5, 4), make_scalar_int(15, 4), false);
        let joined = r1.join(&r2);
        assert_eq!(joined.lo, make_scalar_int(1, 4));
        assert_eq!(joined.hi, make_scalar_int(15, 4));
    }

    #[test]
    fn test_range_join_adjacent() {
        // [1, 5] join [6, 10] should be [1, 10]
        let r1 = Range::new(make_scalar_int(1, 4), make_scalar_int(5, 4), false);
        let r2 = Range::new(make_scalar_int(6, 4), make_scalar_int(10, 4), false);
        let joined = r1.join(&r2);
        assert_eq!(joined.lo, make_scalar_int(1, 4));
        assert_eq!(joined.hi, make_scalar_int(10, 4));
    }

    #[test]
    fn test_range_intersect_singleton() {
        // [5, 5] intersect [3, 7] should be [5, 5]
        let r1 = Range::singleton(make_scalar_int(5, 4), false);
        let r2 = Range::new(make_scalar_int(3, 4), make_scalar_int(7, 4), false);
        let intersected = r1.intersect(r2).unwrap();
        assert_eq!(intersected.lo, intersected.hi);
        assert_eq!(intersected.lo, make_scalar_int(5, 4));
    }

    #[test]
    fn test_range_intersect_singleton_outside() {
        // [5, 5] intersect [10, 20] should be None
        let r1 = Range::singleton(make_scalar_int(5, 4), false);
        let r2 = Range::new(make_scalar_int(10, 4), make_scalar_int(20, 4), false);
        assert!(r1.intersect(r2).is_none());
    }
}
