(** Federer (1969), 4.1.14, pp. 371–372: the
    original Lebesgue-almost-everywhere bound of the actual
    differential persists on every smaller open source.
    Reuse the graph restriction law of 3.1.1,
    p. 209. No derivative bound is imposed
    for the current's variation measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLocal InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanLebesgueDimensions
  MeasureAlmostUP MeasureAlmostBasic CurrentCompactMajorantApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_ae_differential_majorant_open_restriction]:
    the original continuous-majorant hypothesis is local
    on the open source in Federer 4.1.14,
    pp. 371–372. The same actual differential
    graph witness works on W; no total
    derivative representative or new exceptional set is chosen. *)
Theorem current_ae_differential_majorant_open_restriction
    (R:realType) n nu (U W:set (R_n R n))
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hWU:forall x,W x->U x)
    (f:R_n R n->R_n R nu) (sigma:R_n R n->R^o):
  @is_current_ae_differential_majorant R n nu U f sigma->
  @is_current_ae_differential_majorant R n nu W f sigma.
Proof.
move=>hAE.
apply:(@measure_almost_everywhere_mono R (R_n R n)
  (@euclidean_lebesgue_measure R n) (euclidean_lebesgue_is_measure R n)
  _ _ _ hAE)=>x hx hWx.
have[D [hD hCap]]:=hx (@hWU x hWx).
exists D;split;last exact:hCap.
exact:(@norm_differential_restrict R (R_n R n) (R_n R nu)
  (inner_norm (@euclidean_inner_productP R n))
  (inner_norm (@euclidean_inner_productP R nu))
  U W f x D hWU (@hW x hWx) hD).
Qed.
