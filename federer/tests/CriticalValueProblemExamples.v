(** Federer (1969), 3.4.1, p. 310: regression examples for the critical
    source, its image, and finite rank in an unrestricted target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import TensorUP Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP
  LinearRankUP FiniteSourceLinearRank CriticalValueLoci CriticalValueProblem
  CriticalValueDegree CriticalValueDegreeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [constant_nonzero_critical_image]: a rank-zero instance
    of the original sets in 3.4.1, p. 310. The map R^2 -> R with value
    one has the entire plane as critical source and the nonzero singleton
    as image. At class two the announced exponent is one. *)
Example constant_nonzero_critical_image (R:realType):
  @CriticalValueDegree.value R 2 0 2 (erefl true) (erefl true)=(1:R) /\
  @critical_rank_locus R 2 R^o (fun t=>`|t|) setT (fun _=>1) 0=setT /\
  @critical_value_image R 2 R^o (fun t=>`|t|) setT (fun _=>1) 0=[set 1].
Proof.
have hA a (ha:setT a):norm_domain_interior
    (inner_norm (@euclidean_inner_productP R 2)) setT a.
  exists 1;split;first exact:ltr01.
  by move=>h _.
have hC:=@critical_rank_locus_constant R 2 R^o (fun t=>`|t|)
  (@scalar_absolute_value_norm R) setT hA 1 0.
split.
- rewrite critical_value_degree_formula /= subr0 add0r.
  by rewrite divff //;rewrite pnatr_eq0.
split;first exact:hC.
rewrite critical_value_imageE hC.
apply/seteqP;split.
- by move=>y [x _ <-].
- move=>y ->;exists 0;by [].
Qed.

(** Source for [identity_critical_thresholds]: a full-rank instance of
    3.4.1, p. 310. The line identity has empty rank-zero locus and full
    rank-one locus. This also tests uniqueness of the differential. *)
Example identity_critical_thresholds (R:realType):
  let N:=inner_norm (@euclidean_inner_productP R 1) in
  let I:=hom_of_linear (@linear_id R (R_n R 1)) in
  critical_rank_locus N setT I 0=set0 /\
  critical_rank_locus N setT I 1=setT.
Proof.
move=>N I.
have hA a (ha:setT a):norm_domain_interior N setT a.
  exists 1;split;first exact:ltr01.
  by move=>h _.
have hBound:norm_bounded_linear N N I.
  exists 1;split;first exact:ler01.
  by move=>x;rewrite mul1r.
have hRank:has_linear_rank I 1%N.
  apply:(@finite_source_injective_linear_rank R (R_n R 1) (R_n R 1) I 1
    (@coordinate_basis R 1) (@coordinate_basisP R 1)).
  by move=>x y.
have hP:=@critical_rank_locus_linearP R 1 (R_n R 1) N
  (inner_norm_real_norm (@euclidean_inner_productP R 1)) setT hA I hBound 1 hRank.
split;apply/seteqP;split.
- by move=>a /((hP 0 a).1)[_].
- by move=>a [].
- by move=>a _.
- move=>a _;apply:(hP 1 a).2;by split.
Qed.

(** Source for [sequence_target_finite_source_rank]: supporting arbitrary
    Y in 3.4.1, p. 310. The map R -> (nat -> R) sending a scalar to its
    constant sequence has rank one. No finite target basis is supplied. *)
Example sequence_target_finite_source_rank (R:realType):
  exists L:Hom (R_n R 1) (GRing.Lmodule.clone R (nat->R^o) _),
    (forall x j,L x j=x ord0) /\has_linear_rank L 1%N /\
    exists r,has_linear_rank L r /\(r<=1)%N.
Proof.
have hlin:linear (fun x:R_n R 1=>(fun _:nat=>x ord0)).
  by move=>a x y;apply:funext=>j;rewrite !ffunE.
pose L:Hom (R_n R 1) (GRing.Lmodule.clone R (nat->R^o) _):=
  @HomMap R (R_n R 1) (GRing.Lmodule.clone R (nat->R^o) _)
    (fun x=>fun _:nat=>x ord0) (introT (asboolP _) hlin).
have hinj:injective L.
  move=>x y h;apply/ffunP=>i;rewrite (ord1 i).
  exact:(congr1 (fun z=>z 0%N) h).
exists L;split;first by [].
split.
- exact:(@finite_source_injective_linear_rank R (R_n R 1)
    (GRing.Lmodule.clone R (nat->R^o) _) L 1 (@coordinate_basis R 1) (@coordinate_basisP R 1) hinj).
- exact:(@finite_source_linear_rank_exists R (R_n R 1)
    (GRing.Lmodule.clone R (nat->R^o) _) L 1 (@coordinate_basis R 1) (@coordinate_basisP R 1)).
Qed.
