(** Federer (1969), 3.4.8(2),(5), pp. 326, 328:
    the original orthogonal maps induce actual analytic
    germ-ring homomorphisms. Norm preservation proves analyticity;
    all representatives remain behind the pointed pullback seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalMaps OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  NormDifferentialUP NormOpenDomainLaws NormAnalyticUP NormAnalyticLinear AnalyticGermUP
  AnalyticGermRing AnalyticGermMetric PointedAnalyticPullbackUP PointedAnalyticPullbackSealed
  PointedAnalyticPullbackRingMorphism PointedAnalyticPullbackContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrthogonalPullback.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation mapg:=(fun g:O=>@orthogonal_element_map R X B hB n e he g).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].

(** Source for [orthogonal_germ_coordinate_analytic]: each original
    g in O(n) is analytic at zero with its actual
    norm and map, supporting 3.4.8(2),(5), pp. 326, 328. *)
Lemma orthogonal_germ_coordinate_analytic (g:O):
  @norm_analytic_at R X X NX NX hNX hNX setT (mapg g) 0.
Proof.
have hBound:norm_bounded_linear NX NX (mapg g).
  exists 1;split;first exact:ler01.
  move=>x.
  have hNorm:=@orthogonal_map_norm R X X B B hB hB (hom_as_linear (mapg g))
    (@orthogonal_element_orthogonal R X B hB n e he g) x.
  rewrite hom_as_linearE in hNorm.
  by rewrite hNorm mul1r.
exact:((@norm_bounded_linear_analytic R X X NX NX hNX hNX setT
  (fun x _=>norm_full_domain_interior NX x) (mapg g) hBound) 0 Logic.I).
Qed.

(** Source for [orthogonal_germ_coordinate_zero]: the actual
    orthogonal map preserves zero, supporting the original
    origin germ in 3.4.8(2), p. 326. *)
Lemma orthogonal_germ_coordinate_zero (g:O):mapg g 0=0.
Proof. exact:linear0 (mapg g). Qed.

(** Source for [analytic_orthogonal_germ_map]: the original
    O_0(g), supporting I_g in 3.4.8(2), p. 326.
    The actual pointed pullback and its proved arithmetic
    supply the ring homomorphism. *)
Definition analytic_orthogonal_germ_map (g:O):{rmorphism G->G}:=
  @pointed_analytic_germ_ring_pullback R X X NX NX hNX hNX (mapg g) 0 0
    (@PointedAnalyticPullback.map R X X NX NX hNX hNX setT (mapg g) 0 0
      (orthogonal_germ_coordinate_analytic g) (orthogonal_germ_coordinate_zero g))
    (@PointedAnalyticPullback.laws R X X NX NX hNX hNX setT (mapg g) 0 0
      (orthogonal_germ_coordinate_analytic g) (orthogonal_germ_coordinate_zero g)).

(** Source for [analytic_orthogonal_germ_map_specification]: every
    original representative pulls back by actual composition
    with g, supporting 3.4.8(2),(5), pp. 326, 328. *)
Lemma analytic_orthogonal_germ_map_specification (g:O):
  is_pointed_analytic_germ_pullback (mapg g) (analytic_orthogonal_germ_map g).
Proof.
exact:(@PointedAnalyticPullback.laws R X X NX NX hNX hNX setT (mapg g) 0 0
  (orthogonal_germ_coordinate_analytic g) (orthogonal_germ_coordinate_zero g)).
Qed.

(** Source for [analytic_orthogonal_germ_map_continuous]: each
    actual O_0(g) is continuous in the original germ
    metric, supporting 3.4.8(5), p. 328. Joint
    continuity in the germ and g is a further obligation. *)
Lemma analytic_orthogonal_germ_map_continuous (g:O):
  continuous (fun alpha:@analytic_germ_metric R X NX hNX 0=>
    (analytic_orthogonal_germ_map g alpha:@analytic_germ_metric R X NX hNX 0)).
Proof.
exact:(@pointed_analytic_germ_pullback_continuous R X X NX NX hNX hNX setT (mapg g) 0 0
  (analytic_orthogonal_germ_map g) (orthogonal_germ_coordinate_analytic g)
  (orthogonal_germ_coordinate_zero g) (analytic_orthogonal_germ_map_specification g)).
Qed.
End OrthogonalPullback.
