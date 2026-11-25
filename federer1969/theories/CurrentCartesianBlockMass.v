(** Federer (1969), 4.1.8, p. 361: the original
    exterior block inclusions preserve mass and the block
    projections contract it. Reuse the original Euclidean
    block norm laws and the proved 1.8.1 map estimate. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  EuclideanBlockLinearMaps EuclideanBlockNorms CoareaPerturbationBound
  ExteriorGrading ExteriorMaps FiniteExteriorPowers
  CurrentCoefficientNorms CurrentExteriorNonexpansive.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianBlockMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation p := (hom_as_linear (@euclidean_first_block_map R m n)).
Local Notation q := (hom_as_linear (@euclidean_last_block_map R m n)).
Local Notation P := (hom_as_linear (@euclidean_first_injection_map R m n)).
Local Notation Q := (hom_as_linear (@euclidean_last_injection_map R m n)).

(** Source for [current_cartesian_first_projection_mass]:
    the original first projection contracts every exterior
    mass, supporting Federer 4.1.8, p. 361. *)
Lemma current_cartesian_first_projection_mass d (x:exterior_power Z d):
  @current_vector_mass R h2 m d (exterior_power_map p d x)<=@current_vector_mass R h2 (m+n) d x.
Proof.
exact:(@current_exterior_nonexpansive R h2 (m+n) m p
  (fun z=>(@coarea_block_projection_norms R m n z).1) d x).
Qed.

(** Source for [current_cartesian_second_projection_mass]:
    the original second projection contracts every exterior
    mass, supporting Federer 4.1.8, p. 361. *)
Lemma current_cartesian_second_projection_mass d (x:exterior_power Z d):
  @current_vector_mass R h2 n d (exterior_power_map q d x)<=@current_vector_mass R h2 (m+n) d x.
Proof.
exact:(@current_exterior_nonexpansive R h2 (m+n) n q
  (fun z=>(@coarea_block_projection_norms R m n z).2) d x).
Qed.

(** Source for [current_cartesian_first_inclusion_mass]:
    the original first inclusion preserves every exterior
    mass, supporting Federer 4.1.8, p. 361. The
    projection inverse supplies the reverse inequality. *)
Theorem current_cartesian_first_inclusion_mass d (x:exterior_power X d):
  @current_vector_mass R h2 (m+n) d (exterior_power_map P d x)=@current_vector_mass R h2 m d x.
Proof.
apply/eqP;rewrite eq_le;apply/andP;split.
- have hP:forall u,inner_norm (@euclidean_inner_productP R (m+n)) (P u)<=inner_norm (@euclidean_inner_productP R m) u.
    by move=>u;rewrite euclidean_first_injection_norm.
  exact:(@current_exterior_nonexpansive R h2 m (m+n) P hP d x).
- have h:=current_cartesian_first_projection_mass (exterior_power_map P d x).
  by rewrite (@exterior_power_mapK R X Z P p (@euclidean_first_block_injectionK R m n) d) in h.
Qed.

(** Source for [current_cartesian_second_inclusion_mass]:
    the original second inclusion preserves every exterior
    mass, supporting Federer 4.1.8, p. 361. Both
    empty coordinate blocks remain valid. *)
Theorem current_cartesian_second_inclusion_mass d (x:exterior_power Y d):
  @current_vector_mass R h2 (m+n) d (exterior_power_map Q d x)=@current_vector_mass R h2 n d x.
Proof.
apply/eqP;rewrite eq_le;apply/andP;split.
- have hQ:forall u,inner_norm (@euclidean_inner_productP R (m+n)) (Q u)<=inner_norm (@euclidean_inner_productP R n) u.
    by move=>u;rewrite euclidean_last_injection_norm.
  exact:(@current_exterior_nonexpansive R h2 n (m+n) Q hQ d x).
- have h:=current_cartesian_second_projection_mass (exterior_power_map Q d x).
  by rewrite (@exterior_power_mapK R Y Z Q q (@euclidean_last_block_injectionK R m n) d) in h.
Qed.
End CurrentCartesianBlockMass.
