(** Federer (1969), 3.1.13, p. 225:
    the partition functions extend smoothly by zero
    to the entire Euclidean space. The proof uses
    their closed supports contained in the open domain.
    Existing Chapter 2 sealed zero-extension laws are reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  PartialFunctionExtensionUP PartialFunctionExtensionSealed
  ContinuousMultilinearUP NormHigherDifferentialConstant NormClassHigherUP
  NormClassHigherLocal NormClassHigherLocalValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_zero_extended_function]:
    the extension with value zero outside U
    in Federer 3.1.13, p. 225,
    obtained solely from the already sealed
    Chapter 2 extension interfaces. *)
Definition norm_zero_extended_function (X : Type) (Y : zmodType)
    (U : set X) (f : X->Y) : X->Y :=
  @PartialFunctionExtension.value X Y
    (partial_function_zero_extension 0 U (partial_function_total f)) 0.

(** Source for [norm_zero_extended_function_on]:
    the zero extension preserves the original
    function on U, Federer 3.1.13, p. 225. *)
Lemma norm_zero_extended_function_on (X : Type) (Y : zmodType)
    (U : set X) (f : X->Y) x :
  U x -> norm_zero_extended_function U f x=f x.
Proof.
move=>hx; apply: (@PartialFunctionExtension.laws X Y
  (partial_function_zero_extension 0 U (partial_function_total f)) 0 x (f x)).
apply/partial_function_zero_extension_graph; left; split; first exact hx; by [].
Qed.

(** Source for [norm_zero_extended_function_off]:
    the extension has value zero outside U,
    Federer 3.1.13, p. 225. *)
Lemma norm_zero_extended_function_off (X : Type) (Y : zmodType)
    (U : set X) (f : X->Y) x :
  ~U x -> norm_zero_extended_function U f x=0.
Proof.
move=>hx; apply: (@PartialFunctionExtension.laws X Y
  (partial_function_zero_extension 0 U (partial_function_total f)) 0 x 0).
apply/partial_function_zero_extension_graph; right; by split.
Qed.

(** Source for [norm_class_higher_zero_extension]:
    extending a smooth function by zero is
    smooth when its support lies in a
    closed subset of the original open domain,
    supporting the final assertion of Federer
    3.1.13, p. 225. This
    is a local argument and needs no
    uniform positive distance from the boundary. *)
Theorem norm_class_higher_zero_extension (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (U K : set X) (f : X->Y) k :
  @closed [the topologicalType of real_norm_metric_space hNX] K ->
  K `<=` U -> (forall x, U x -> ~K x -> f x=0) ->
  norm_class_higher NX NY ev ZN U f k ->
  norm_class_higher NX NY ev ZN (fun _=>True) (norm_zero_extended_function U f) k.
Proof.
move=>hK hKU hf hc.
apply: (norm_class_higher_local hNX hNY hZ)=>a _.
case:(pselect (U a))=>[ha|ha].
- exists U; split; first exact ha; split; first by move=>x hx.
  apply: (@norm_class_higher_domain_agreement R X Y NX NY hNX hNY
    Z ev ZN hZ U f (norm_zero_extended_function U f) k _ hc).
  by move=>x hx; rewrite norm_zero_extended_function_on.
- pose O := ~`K.
  have hOa : O a by move=>hk; exact: (ha (hKU a hk)).
  have hOopen := closed_openC hK.
  have hopen x (hx : O x) : norm_domain_interior NX O x.
    apply: (norm_domain_interior_neighbourhood hNX O x).2.
    by move:hOopen; rewrite openE; apply.
  exists O; split; first exact hOa; split; first by move=>x hx.
  have hz := @norm_class_infinity_constant R X Y NX NY hNX hNY Z ev ZN hZ
    O hopen 0 k.
  apply: (@norm_class_higher_domain_agreement R X Y NX NY hNX hNY
    Z ev ZN hZ O (fun _=>0) (norm_zero_extended_function U f) k _ hz).
  move=>x hx; symmetry; case:(pselect (U x))=>[hux|hux].
  + rewrite norm_zero_extended_function_on //; exact: (hf x hux hx).
  + exact: (norm_zero_extended_function_off f hux).
Qed.
