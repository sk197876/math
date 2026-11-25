(** Federer (1969), 3.3.3, p. 288: actual regressions
    for an empty source, the sole point of R^0 and the
    nonempty punctured whole-line fibre of the zero projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions reals topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanOneCoordinate EuclideanOneNormDifferential EuclideanProjectionSpace
  StructureFibreAccumulation StructureFibreIncidence StructureFibreSuslin
  StructureConeDensityValues SuslinSetUP TopologicalBorel BorelClosedProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_empty_fibre_accumulation]: the
    empty-source endpoint of Federer 3.3.3, p. 288.
    No actual punctured affine fibre contains a source point. *)
Example structure_empty_fibre_accumulation (R:realType) n m
    (hmn:(m<=n)%N):
  @structure_fibre_accumulation R n m hmn set0=set0.
Proof.
apply/seteqP; split=>z hz; last by [].
have [x [hx _]]:=(structure_fibre_accumulation_reciprocals hmn set0 z).1 hz 0%N.
exact:hx.
Qed.

(** Source for [structure_zero_ambient_no_accumulation]:
    the actual zero-dimensional endpoint of Federer 3.3.3,
    p. 288. The whole source is nonempty, but its
    punctured fibre is empty because its sole point is
    excluded, so it is not an accumulation point. *)
Example structure_zero_ambient_no_accumulation (R:realType)
    (p:euclidean_projection_space R 0 0):
  ~structure_fibre_accumulation (leqnn 0) setT (0,p).
Proof.
move=>h; have [x [_ [_ /andP [hPos _]]]]:=
  (structure_fibre_accumulation_reciprocals (leqnn 0) setT (0,p)).1 h 0%N.
have hx:x=0 by apply/ffunP=>i; have hi:=ltn_ord i; rewrite ltn0 in hi.
by rewrite hx subrr inner_norm0 ltxx in hPos.
Qed.

(** Source for [structure_actual_line_fibre_accumulation]:
    the nonempty fibre endpoint of Federer 3.3.3,
    p. 288. The actual projection of R^1 to R^0
    has positive reciprocal half-scale points in its
    punctured fibre at zero. Its full locus is Suslin. *)
Example structure_actual_line_fibre_accumulation (R:realType)
    (p:euclidean_projection_space R 1 0):
  structure_fibre_accumulation (leq0n 1) setT (0,p) /\
  is_suslin_set R (@structure_fibre_accumulation R 1 0 (leq0n 1) setT).
Proof.
split.
- apply/(structure_fibre_accumulation_reciprocals (leq0n 1) setT (0,p))=>i.
  pose t:=((i.+1)%:R:R)^-1.
  have ht:0<t by rewrite /t invr_gt0 ltr0n.
  have hHalf:0<t/2<t:=structure_density_positive_half_bounds ht.
  exists (euclidean_one_embed (t/2)); split=>//; split.
  + apply/ffunP=>j; have hj:=ltn_ord j; by rewrite ltn0 in hj.
  + rewrite subr0 euclidean_one_norm_coordinate /euclidean_one_embed ffunE
      ger0_norm; first exact:hHalf.
    exact:(ltW (andP hHalf).1).
- apply:(@federer_3_3_3 R 1 0 (leq0n 1) setT).
  apply:metric_borel_suslin; exact:(open_borel_set openT).
Qed.
