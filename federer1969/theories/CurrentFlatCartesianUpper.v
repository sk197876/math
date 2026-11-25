(** Federer (1969), 4.1.12, p. 369: the
    first Cartesian flat estimate for arbitrary original
    currents. Combine the finite decomposition bound
    with the original nonnegative extended-real cases.
    Keep the ordinary partial-product domain explicit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces SmoothCompactSet
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentBoundary CurrentMassSealed NormalCurrentsUP
  CurrentNormalMass CurrentFlatNorm CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic
  CurrentFlatCartesianFiniteUpper.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatCartesianUpper.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variables (KA:smooth_compact_set hNX A) (KB:smooth_compact_set hNY B)
  (KAB:smooth_compact_set hNZ AB).
Hypothesis hKAB:smooth_compact_carrier KAB=
  @euclidean_cartesian_set R m n (smooth_compact_carrier KA) (smooth_compact_carrier KB).
Local Notation CA d := (@current_space R h2 m A hA d).
Local Notation CB d := (@current_space R h2 n B hB d).
Local Notation MA d := (@CurrentMass.value R h2 m d A hA).
Local Notation MB d := (@CurrentMass.value R h2 n d B hB).
Local Notation MC d := (@CurrentMass.value R h2 (m+n) d AB hAB).
Local Notation P k l := (@CartesianCurrentProduct.value R h2 m n k l A B hA hB).
Local Notation bdA d := (@current_boundary R h2 m d A hA).
Local Notation bdB d := (@current_boundary R h2 n d B hB).
Local Notation bdC d := (@current_boundary R h2 (m+n) d AB hAB).
Local Notation suppA d := (@current_support R h2 m A hA d).
Local Notation suppB d := (@current_support R h2 n B hB d).
Local Notation suppC d := (@current_support R h2 (m+n) AB hAB d).

Local Notation N d := (@current_normal_mass R h2 m A hA d).
Local Notation FD d := (@current_flat_norm R h2 n d B hB KB).
(** Source for [current_flat_cartesian_upper]:
    F_(C times D)(S times T)<=N(S)F_D(T) if
    spt S is contained in C, the first printed
    product inequality in Federer 4.1.12, p. 369.
    No normality or finite-mass hypothesis is added;
    infinite values use the original partial product. *)
Theorem current_flat_cartesian_upper i j (S:CA i) (T:CB j):
  suppA i S `<=` smooth_compact_carrier KA->
  mule_def (N i S) (FD j T)->
  (@current_flat_norm R h2 (m+n) (i+j) AB hAB KAB (P i j S T)<=N i S * FD j T)%E.
Proof.
move=>hSupport hDef.
have hN0:=@current_normal_mass_nonnegative R h2 m A hA i S.
have hT0:=@current_flat_dual_nonnegative R h2 n j B hB KB (@current_value R h2 n B hB j T).
change (is_true (0<=FD j T)%E) in hT0.
case:(ltP (N i S) (+oo)%E)=>hNFinite.
- case:(ltP (FD j T) (+oo)%E)=>hTFinite.
  + have hNNumber:N i S \is a fin_num by rewrite (ge0_fin_numE hN0).
    pose a:=fine (N i S).
    have hNValue:N i S=a%:E by rewrite /a fineK.
    have [b [hb hTValue]]:=@current_flat_dual_finite_value R h2 n j B hB KB
      (@current_value R h2 n B hB j T) hTFinite.
    have hFlat:FD j T=b%:E:=hTValue.
    rewrite hNValue hFlat -EFinM.
    exact:(@current_flat_cartesian_finite_upper R h2 m n A B hA hB KA KB KAB hKAB i j S T a b
      hNValue hFlat hSupport).
  + have hTInfinity:FD j T= (+oo)%E by apply/eqP;rewrite eq_le leey hTFinite.
    case:(eqVneq (N i S) 0)=>hNZ.
    * move:hDef;by rewrite hNZ hTInfinity /mule_def /= eqxx.
    * have hNPos:(0<N i S)%E by rewrite lt_neqAle eq_sym hNZ hN0.
      rewrite hTInfinity (gt0_muley hNPos);exact:leey.
- have hNInfinity:N i S= (+oo)%E by apply/eqP;rewrite eq_le leey hNFinite.
  case:(eqVneq (FD j T) 0)=>hTZ.
  + move:hDef;by rewrite hNInfinity hTZ /mule_def /= eqxx.
  + have hTPos:(0<FD j T)%E by rewrite lt_neqAle eq_sym hTZ hT0.
    rewrite hNInfinity (gt0_mulye hTPos);exact:leey.
Qed.
End CurrentFlatCartesianUpper.
