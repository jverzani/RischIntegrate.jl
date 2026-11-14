# ---------------------------------------------------------------------------
# Per-call state (SymPy #10450, #10449: concurrent integrate calls). The steps keep flags and counters for the
# call in progress: a substitution not re-entered (RECIPROCAL, ATAN_SUBST, …), nesting depths (RISCH_DEPTH,
# USUB_DEPTH, …), signals read by an outer step (PR_ROOTSUM, HALF_ANGLE_FORMS, NEG_LOG_DROPPED). They were
# module-level Refs, shared by every task: two calls
# on different threads could skip each other's steps or answer checks. They are fields of one `CallState`, made by
# the outermost `risch_integrate` and held in a ScopedValue for its dynamic extent; each name is a `StateField`,
# read and written as before (`RISCH_DEPTH[] += 1`). Outside any call (an internal function run directly, as in
# the tests) a module-level state stands in, as the Refs did.
# The settings HYP_ANSWERS and CONJ_CHECK stay module-level Refs: they are set by the user, not by a call. The
# moduli HYP_MOD and HYP_NF stay Refs too, under a lock (hyperelliptic.jl: they are read in every operation).
# ---------------------------------------------------------------------------
mutable struct CallState
    opaque_const_radicals::Bool
    const_scaling::Bool
    reciprocal::Bool
    pxparts::Bool
    xparts::Bool
    tower_radical::Bool
    ec_active::Bool
    half_angle_forms::Int
    usub_depth::Int
    nested_subst::Bool
    pair_subst::Int
    outer_check::Bool
    expr_retry::Bool
    mn_active::Bool
    pr_defer::Bool
    pr_outer::Bool
    pr_rootsum::Bool
    risch_depth::Int
    linear_shift::Bool
    ci_check::Bool
    ek_active::Bool
    neg_log_dropped::Int
    bn_shifted::Bool
    atan_subst::Bool
    parts::Bool
    ah_active::Bool
    imag_param::Bool
    erf_depth::Int
    sum_split::Int
end
CallState() = CallState(false, false, false, false, false, false, false, 0, 0, false, 0, false, false, false, false, false,
                        false, 0, false, false, false, 0, false, false, false, false, false, 0, 0)

const CALL_STATE = Base.ScopedValues.ScopedValue{Union{Nothing,CallState}}(nothing)
const DIRECT_STATE = CallState()                         # outside any risch_integrate call
@inline call_state() = (s = CALL_STATE[]; s === nothing ? DIRECT_STATE : s)
# run g() with a fresh state, unless a call is already in progress
in_call_state(g) = CALL_STATE[] === nothing ? Base.ScopedValues.with(g, CALL_STATE => CallState()) : g()

struct StateField{F} end
@inline Base.getindex(::StateField{F}) where {F} = getfield(call_state(), F)
@inline Base.setindex!(::StateField{F}, v) where {F} = (setproperty!(call_state(), F, v); v)

const OPAQUE_CONST_RADICALS = StateField{:opaque_const_radicals}()
const CONST_SCALING = StateField{:const_scaling}()
const RECIPROCAL = StateField{:reciprocal}()
const PXPARTS = StateField{:pxparts}()
const XPARTS = StateField{:xparts}()
const TOWER_RADICAL = StateField{:tower_radical}()
const EC_ACTIVE = StateField{:ec_active}()
const HALF_ANGLE_FORMS = StateField{:half_angle_forms}()
const USUB_DEPTH = StateField{:usub_depth}()
const NESTED_SUBST = StateField{:nested_subst}()
const PAIR_SUBST = StateField{:pair_subst}()
const OUTER_CHECK = StateField{:outer_check}()
const EXPR_RETRY = StateField{:expr_retry}()
const MN_ACTIVE = StateField{:mn_active}()
const PR_DEFER = StateField{:pr_defer}()
const PR_OUTER = StateField{:pr_outer}()
const PR_ROOTSUM = StateField{:pr_rootsum}()
const RISCH_DEPTH = StateField{:risch_depth}()
const LINEAR_SHIFT = StateField{:linear_shift}()
const CI_CHECK = StateField{:ci_check}()
const EK_ACTIVE = StateField{:ek_active}()
const NEG_LOG_DROPPED = StateField{:neg_log_dropped}()
const BN_SHIFTED = StateField{:bn_shifted}()
const ATAN_SUBST = StateField{:atan_subst}()
const PARTS = StateField{:parts}()
const AH_ACTIVE = StateField{:ah_active}()
const IMAG_PARAM = StateField{:imag_param}()
const ERF_DEPTH = StateField{:erf_depth}()
const SUM_SPLIT = StateField{:sum_split}()
