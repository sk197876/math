(** Federer (1969), 4.1.12, p. 369: the
    attained original decomposition gives the first
    Cartesian flat estimate whenever its two numerical
    factors are finite. No representation or normality
    premise is added to the original currents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces SmoothCompactSet
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentBoundary CurrentMassSealed CurrentMassBasic
  NormalCurrentsUP CurrentNormalMass CurrentFlatNorm CurrentFlatDualSeminormSealed CurrentFlatDualSeminormBasic
  CurrentFlatHahnBanachDecomposition CurrentCartesianFlatDecompositionPositive CurrentCartesianFlatDecompositionZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentFlatCartesianFiniteUpper.
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
(** Source for [current_flat_cartesian_finite_upper]:
    F_(C times D)(S times T)<=n t for N(S)=n
    and F_D(T)=t, with spt S contained in C,
    the finite part of the first original product
    inequality in Federer 4.1.12, p. 369.
    The original zero-degree boundary exception is retained. *)
Theorem current_flat_cartesian_finite_upper i j (S:CA i) (T:CB j) nval t:
  N i S=nval%:E->FD j T=t%:E->
  suppA i S `<=` smooth_compact_carrier KA->
  (@current_flat_norm R h2 (m+n) (i+j) AB hAB KAB (P i j S T)<=(nval*t)%:E)%E.
Proof.
move=>hNValue hTValue hSupport.
have hn:0<=nval.
  have h:=@current_normal_mass_nonnegative R h2 m A hA i S.
  by rewrite hNValue lee_fin in h.
have [A0 [B0 [hDecomposition [hA0 [hB0 hCost]]]]]:=
  @current_flat_hahn_banach_decomposition R h2 n j B hB KB T t hTValue.
have hCostFinite:(MB j A0+MB j.+1 B0 < +oo)%E:=le_lt_trans hCost (ltry t).
have hA0Finite:(MB j A0 < +oo)%E:=le_lt_trans
  (leeDl (MB j A0) (@current_mass_nonnegative R h2 n j.+1 B hB B0)) hCostFinite.
have hB0Finite:(MB j.+1 B0 < +oo)%E:=le_lt_trans
  (leeDr (MB j.+1 B0) (@current_mass_nonnegative R h2 n j B hB A0)) hCostFinite.
have [r [hr hMassA0]]:=@current_finite_mass_value R h2 n j B hB A0 hA0Finite.
have [s [hs hMassB0]]:=@current_finite_mass_value R h2 n j.+1 B hB B0 hB0Finite.
have hRS:r+s<=t by move:hCost;rewrite hMassA0 hMassB0 -EFinD lee_fin.
case:i S hNValue hSupport=>[|k] S hNValue hSupport.
- have hMassS:MA 0%N S=nval%:E:=hNValue.
  have hBound:=@current_cartesian_flat_decomposition_zero R h2 m n j A B hA hB KA KB KAB hKAB
    S A0 B0 nval r s hMassS hMassA0 hMassB0 hSupport hA0 hB0.
  rewrite -hDecomposition in hBound.
  apply:(le_trans hBound);rewrite lee_fin.
  have h:=ler_wpM2l hn hRS;by rewrite mulrDr in h.
- change ((MA k.+1 S+MA k (bdA k S))%E=nval%:E) in hNValue.
  have hNFinite:(MA k.+1 S+MA k (bdA k S) < +oo)%E by rewrite hNValue;exact:ltry.
  have hSFinite:(MA k.+1 S < +oo)%E:=le_lt_trans
    (leeDl (MA k.+1 S) (@current_mass_nonnegative R h2 m k A hA (bdA k S))) hNFinite.
  have hBdFinite:(MA k (bdA k S) < +oo)%E:=le_lt_trans
    (leeDr (MA k (bdA k S)) (@current_mass_nonnegative R h2 m k.+1 A hA S)) hNFinite.
  have [a [ha hMassS]]:=@current_finite_mass_value R h2 m k.+1 A hA S hSFinite.
  have [b [hb hMassBd]]:=@current_finite_mass_value R h2 m k A hA (bdA k S) hBdFinite.
  have hAB:a+b=nval.
    rewrite hMassS hMassBd -EFinD in hNValue;exact:(EFin_inj hNValue).
  have hBound:=@current_cartesian_flat_decomposition_positive R h2 m n k j A B hA hB KA KB KAB hKAB
    S A0 B0 a b r s hMassS hMassBd hMassA0 hMassB0 hSupport hA0 hB0.
  rewrite -hDecomposition in hBound.
  apply:(le_trans hBound);rewrite lee_fin.
  have hEnlarge:a*r+b*s+a*s<=(a+b)*(r+s).
    have hBR:=mulr_ge0 hb hr.
    rewrite !mulrDl !mulrDr;lra.
  apply:(le_trans hEnlarge).
  rewrite hAB;exact:(ler_wpM2l hn hRS).
Qed.
End CurrentFlatCartesianFiniteUpper.
