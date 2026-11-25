(** Federer (1969), 1.9.1, p. 42: induced maps on each symmetric power.
    Supporting identity, composition, and injection laws. Arbitrary vector
    spaces over any field are allowed. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import TensorUP AlgebraUP GradedAlgebra GradedComponents
  LinearRetraction SymmetricAlgebra SymmetricGrading SymmetricMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_power_map_ext]: Federer 1.9.1, p. 42,
    induced degree maps. Supporting extensionality: equal linear maps
    induce equal maps on every symmetric power. *)
Lemma symmetric_power_map_ext (K : fieldType) (V W : lmodType K)
    (f g : {linear V -> W}) : f =1 g -> forall m,
  symmetric_power_map f m =1 symmetric_power_map g m.
Proof.
move=> h m x; apply: val_inj.
exact (@symmetric_algebra_map_eq K V W f g h (component_val x)).
Qed.

(** Source for [symmetric_power_map_identity]: Federer 1.9.1, p. 42, induced
    degree maps. The identity map induces the identity on each power *)
Lemma symmetric_power_map_identity (K : fieldType) (V : lmodType K) m x :
  symmetric_power_map (linear_id V) m x = x.
Proof. apply: val_inj; exact (@symmetric_algebra_map_id K V (component_val x)). Qed.

(** Source for [symmetric_power_map_composition]: Federer 1.9.1, p. 42,
    induced degree maps. Taking symmetric powers commutes with composition *)
Lemma symmetric_power_map_composition (K : fieldType) (V U W : lmodType K)
    (f : {linear V -> U}) (g : {linear U -> W}) m x :
  symmetric_power_map g m (symmetric_power_map f m x) =
    symmetric_power_map (linear_comp g f) m x.
Proof. apply: val_inj; exact (@symmetric_algebra_map_comp K V U W f g (component_val x)). Qed.

(** Source for [symmetric_algebra_mapK]: Federer 1.9.1, p. 42, supporting
    cancellation law for induced maps. A left inverse induces a left
    inverse. *)
Lemma symmetric_algebra_mapK (K : fieldType) (V W : lmodType K)
    (f : {linear V -> W}) (g : {linear W -> V}) (hfg : cancel f g) :
  cancel (symmetric_algebra_map f) (symmetric_algebra_map g).
Proof.
move=> x; rewrite symmetric_algebra_map_comp.
rewrite (@symmetric_algebra_map_eq K V V (linear_comp g f) (linear_id V) hfg).
exact: symmetric_algebra_map_id.
Qed.

(** Source for [symmetric_power_mapK]: Federer 1.9.1, p. 42, supporting
    degree-wise cancellation: a left inverse induces a left inverse on every
    symmetric power. *)
Lemma symmetric_power_mapK (K : fieldType) (V W : lmodType K)
    (f : {linear V -> W}) (g : {linear W -> V}) (hfg : cancel f g) m :
  cancel (symmetric_power_map f m) (symmetric_power_map g m).
Proof.
move=> x; apply: val_inj.
exact (@symmetric_algebra_mapK K V W f g hfg (component_val x)).
Qed.

(** Source for [symmetric_power_map_injective]: Federer 1.9.1, p. 42,
    supporting injectivity of induced degree maps. No finite dimension is
    required. *)
Theorem symmetric_power_map_injective (K : fieldType) (V W : lmodType K)
    (f : {linear V -> W}) (hf : injective f) m :
  injective (symmetric_power_map f m).
Proof.
apply: can_inj (@symmetric_power_mapK K V W f (linear_retraction hf)
  (linear_retractionK hf) m).
Qed.
