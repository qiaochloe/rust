//! Integer range analysis

#![allow(dead_code, unused_imports, unused_variables, unreachable_code, unused_mut)] // TODO: remove

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
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_mir_dataflow::fmt::DebugWithContext;
use rustc_mir_dataflow::lattice::{FlatSet, HasBottom};
use rustc_mir_dataflow::value_analysis::{
    Map, PlaceIndex, State, TrackElem, ValueOrPlace, debug_with_context,
};
use rustc_mir_dataflow::{Analysis, ResultsVisitor, visit_reachable_results};
use rustc_span::DUMMY_SP;
use tracing::{debug, debug_span, instrument};

pub(super) struct IntegerRange;

impl<'tcx> crate::MirPass<'tcx> for IntegerRange {
    // fn name(&self) -> &'static str {
    //     const { simplify_pass_type_name(std::any::type_name::<Self>()) }
    // }

    // fn profiler_name(&self) -> &'static str {
    //     to_profiler_name(self.name())
    // }

    /// Returns `true` if this pass is enabled with the current combination of compiler flags.
    // fn is_enabled(&self, _sess: &Session) -> bool {
    //     true
    // }

    /// Returns `true` if this pass can be overridden by `-Zenable-mir-passes`. This should be
    /// true for basically every pass other than those that are necessary for correctness.
    // fn can_be_overridden(&self) -> bool {
    //     true
    // }

    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) { todo!(); }

    // fn is_mir_dump_enabled(&self) -> bool {
    //     true
    // }

    /// Returns `true` if this pass must be run (i.e. it is required for soundness).
    /// For passes which are strictly optimizations, this should return `false`.
    /// If this is `false`, `#[optimize(none)]` will disable the pass.
    fn is_required(&self) -> bool {
        false
    }
}


// TODO: fill out struct
struct IntegerRangeAnalysis<'tcx>{

    map: Map<'tcx>,
}

impl<'tcx> Analysis<'tcx> for IntegerRangeAnalysis<'tcx> {
    // TODO: define proper domain
    type Domain = State<FlatSet<Scalar>>;

    const NAME: &'static str = "IntegerRangeAnalysis";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        todo!()
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        todo!()
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

impl<'tcx> IntegerRangeAnalysis<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        todo!()
    }

    fn handle_statement(&self, statement: &Statement<'tcx>, state: &mut State<FlatSet<Scalar>>) {
        todo!();
    }

    fn handle_intrinsic(&self, intrinsic: &NonDivergingIntrinsic<'tcx>) {
        todo!();
    }

    fn handle_operand(
        &self,
        operand: &Operand<'tcx>,
        state: &mut State<FlatSet<Scalar>>,
    ) -> ValueOrPlace<FlatSet<Scalar>> {
        todo!();
    }

    fn handle_terminator<'mir>(
        &self,
        terminator: &'mir Terminator<'tcx>,
        state: &mut State<FlatSet<Scalar>>,
    ) -> TerminatorEdges<'mir, 'tcx> {
        todo!();
    }

    fn handle_call_return(
        &self,
        return_places: CallReturnPlaces<'_, 'tcx>,
        state: &mut State<FlatSet<Scalar>>,
    ) {
        todo!();
    }

    fn handle_set_discriminant(
        &self,
        place: Place<'tcx>,
        variant_index: VariantIdx,
        state: &mut State<FlatSet<Scalar>>,
    ) {
        todo!();
    }

    fn handle_assign(
        &self,
        target: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        state: &mut State<FlatSet<Scalar>>,
    ) {
        todo!();
    }

    fn handle_rvalue(
        &self,
        rvalue: &Rvalue<'tcx>,
        state: &mut State<FlatSet<Scalar>>,
    ) -> ValueOrPlace<FlatSet<Scalar>> {
        todo!();
    }

    fn handle_constant(
        &self,
        constant: &ConstOperand<'tcx>,
        _state: &mut State<FlatSet<Scalar>>,
    ) -> FlatSet<Scalar> {
        todo!();
    }

    fn handle_switch_int<'mir>(
        &self,
        discr: &'mir Operand<'tcx>,
        targets: &'mir SwitchTargets,
        state: &mut State<FlatSet<Scalar>>,
    ) -> TerminatorEdges<'mir, 'tcx> {
        todo!();
    }

    /// The caller must have flooded `place`.
    fn assign_operand(
        &self,
        state: &mut State<FlatSet<Scalar>>,
        place: PlaceIndex,
        operand: &Operand<'tcx>,
    ) {
        todo!();
    }

    /// The caller must have flooded `place`.
    fn assign_constant(
        &self,
        state: &mut State<FlatSet<Scalar>>,
        place: PlaceIndex,
        mut operand: OpTy<'tcx>,
        projection: &[PlaceElem<'tcx>],
    ) {
        todo!();
    }

    fn binary_op(
        &self,
        state: &mut State<FlatSet<Scalar>>,
        op: BinOp,
        left: &Operand<'tcx>,
        right: &Operand<'tcx>,
    ) -> (FlatSet<Scalar>, FlatSet<Scalar>) {
        todo!();
    }

    fn eval_operand(
        &self,
        op: &Operand<'tcx>,
        state: &mut State<FlatSet<Scalar>>,
    ) -> FlatSet<ImmTy<'tcx>> {
        todo!();
    }

    fn eval_discriminant(&self, enum_ty: Ty<'tcx>, variant_index: VariantIdx) -> Option<Scalar> {
        todo!();
    }

    fn wrap_immediate(&self, imm: Immediate) -> FlatSet<Scalar> {
        todo!();
    }
}

/// This is used to visualize the dataflow analysis.
impl<'tcx> DebugWithContext<IntegerRangeAnalysis<'tcx>> for State<FlatSet<Scalar>> {
    fn fmt_with(&self, ctxt: &IntegerRangeAnalysis<'tcx>, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            State::Reachable(values) => debug_with_context(values, None, &ctxt.map, f),
            State::Unreachable => write!(f, "unreachable"),
        }
    }

    fn fmt_diff_with(
        &self,
        old: &Self,
        ctxt: &IntegerRangeAnalysis<'tcx>,
        f: &mut Formatter<'_>,
    ) -> std::fmt::Result {
        match (self, old) {
            (State::Reachable(this), State::Reachable(old)) => {
                debug_with_context(this, Some(old), &ctxt.map, f)
            }
            _ => Ok(()), // Consider printing something here.
        }
    }
}
