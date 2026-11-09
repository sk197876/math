(** Federer (1969), 3.4.2(7), p. 312: the compact base case mu=nu. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannSubspaces GrassmannAbbreviations EuclideanInnerProduct
  HilbertFormCompactness NormMetric RealNormUP CriticalManifoldFamilyUP
  CriticalManifoldClassLaws CriticalFlatPiecesUP CriticalCodimensionChart
  CriticalDiscreteOscillation PositiveRightOrderLimit CriticalOscillation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_minimal_dimension_compact_piece]: the complete
    compact base case mu=nu in the induction of 3.4.2(7), p. 312.
    The original pair (S,C) belongs to Ψ. A positive-dimensional chart
    has ker p=Z; a zero-dimensional manifold has a uniform isolation
    scale on C. The same pair controls every function in Φ. *)
Theorem critical_minimal_dimension_compact_piece (R:realType) m d
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:G (R_n R m) d) k (S C:set (R_n R m)):
  critical_manifold_family Z (m-d) k S ->C `<=` S ->
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  is_critical_flat_piece hNY Z (m-d) S C k S C.
Proof.
move=>hFamily hCS hC.
have hOne:=@critical_manifold_family_lower_class R m d Z (m-d) k 1 S
  (erefl true) hFamily.2.1 hFamily.
split.
- exists (m-d)%N;split;[exact:leqnn|exact:hOne].
split;first by move=>x.
split;first exact:hC.
split;first by move=>x hx;split;[exact:hCS x hx|exact:hx].
move=>f hPhi.
case:(posnP (m-d))=>[hZero|hPositive].
- have hS:=hFamily.2.2.1;rewrite hZero in hS.
  exact:(@critical_zero_manifold_eta_zero_limit R m k Y NY (grassmann_val Z)
    S C f k%:R hS hCS hC).
- have [hZero|[p [g hChart]]]:=hFamily.2.2.2.
  + by rewrite hZero in hPositive.
  + apply:(@eventually_zero_positive_cutoff_limit R
      (fun delta=>critical_eta NY (grassmann_val Z) S C f k%:R delta) 1
      (@ltr01 R))=>delta hdelta hsmall.
    exact:(@critical_codimension_eta_zero R m d k Y NY Z S C p g f k%:R delta hChart hCS).
Qed.
