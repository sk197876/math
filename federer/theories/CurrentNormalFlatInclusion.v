(** Federer (1969), 4.1.14, p. 371: the normal currents form
    the original dense linear domain for the extension to
    F_(m,K)(U). Both carriers and their inclusions are the
    existing opaque spaces; no new completion is constructed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom Bilinear ModuleQuotient RealNormUP NormMetric
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentSpaces SmoothCompactSet NormalCurrentsUP
  NormalCurrentSpaces FlatCurrentsUP FlatCurrentFinite FlatCurrentClosure
  FlatCurrentSpaces LinearSubspaceRepresentationUP LinearSubspaceLiftSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentNormalFlatInclusion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable K:smooth_compact_set
  (inner_norm_real_norm (@euclidean_inner_productP R n)) U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation A:=(@supported_normal_current_space R h2 n U hU m K).
Local Notation V:=(@flat_current_space R h2 n m U hU K).
Local Notation incA:=(@supported_normal_current_inclusion R h2 n U hU m K).
Local Notation incV:=(@flat_current_inclusion R h2 n m U hU K).
Local Notation hA:=(@supported_normal_current_space_laws R h2 n U hU m K).
Local Notation hV:=(@flat_current_space_laws R h2 n m U hU K).
Local Notation Flat:=(@flat_current_subspace R h2 n m U hU K).
Local Notation N:=(@flat_current_norm R h2 n m U hU K).

(** Source for [current_normal_flat_inclusion_member]: the
    actual normal inclusion takes values in F_(m,K)(U),
    by 4.1.12, p. 368, as used for the bounded extension
    in Federer 4.1.14, p. 371. *)
Lemma current_normal_flat_inclusion_member a:Flat (incA a).
Proof.
apply:(@supported_normal_current_is_flat R h2 n m U hU K (incA a)).
exact:subspace_representation_member hA a.
Qed.

(** Source for [current_normal_flat_inclusion]: the original
    linear inclusion of N_(m,K)(U) in F_(m,K)(U), supporting
    Federer 4.1.14, p. 371. Reuse the opaque corestriction
    of the original inclusion, with its independently proved range. *)
Definition current_normal_flat_inclusion:Hom A V:=
  @LinearSubspaceLift.map R A V C Flat incV hV incA
    current_normal_flat_inclusion_member.
Local Notation i:=current_normal_flat_inclusion.

(** Source for [current_normal_flat_inclusion_value]: inclusion
    into actual currents is unchanged, supporting the dense-domain
    extension in Federer 4.1.14, p. 371. *)
Lemma current_normal_flat_inclusion_value a:incV (i a)=incA a.
Proof.
exact:(@LinearSubspaceLift.evaluation R A V C Flat incV hV incA
  current_normal_flat_inclusion_member a).
Qed.

(** Source for [current_normal_flat_inclusion_dense]: the
    original normal domain is F_K dense in its flat closure,
    Federer 4.1.12, p. 368, used for the unique bounded
    linear extension in 4.1.14, p. 371. The estimate is
    on the actual opaque flat carrier, with its original norm. *)
Theorem current_normal_flat_inclusion_dense z epsilon:
  0<epsilon->exists a:A,N (z-i a)<epsilon.
Proof.
move=>hEpsilon.
have hFlat:=subspace_representation_member hV z.
have[T [hNormal hError]]:=hFlat epsilon hEpsilon.
have[a hCurrent]:=subspace_representation_full hA hNormal.
exists a.
have hValue:=@flat_current_norm_value R h2 n m U hU K (z-i a).
rewrite (linB (hom_linear incV)) current_normal_flat_inclusion_value hCurrent in hValue.
by move:hError;rewrite hValue lte_fin.
Qed.
End CurrentNormalFlatInclusion.
