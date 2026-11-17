(** Supporting algebra for Federer (1969), 3.4.8(5), p. 328.
    Transport the original opaque ideal powers under a ring map.
    Independent least-ideal product laws prove this connection;
    no quotient-power formula is supplied as a premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP NoetherianRingSurjection
  CommutativeIdealPowersSealed CommutativeIdealPowersLaws
  CommutativeIdealProductSealed CommutativeIdealProductLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [commutative_ideal_power_ring_map]: supporting
    original quotient-filtration connection for the auxiliary sentence
    in Federer 3.4.8(5), p. 328. If a ring map carries I into J,
    it carries every original I-power into the same J-power. *)
Theorem commutative_ideal_power_ring_map (A C:comNzRingType) (f:{rmorphism A->C})
    (I:set A) (J:set C):
  (forall a:A,I a ->J (f a)) ->forall k a,
  @CommutativeIdealPowers.value A I k a ->@CommutativeIdealPowers.value C J k (f a).
Proof.
move=>hImage.
pose P:=@CommutativeIdealPowers.value A I.
pose Q:=@CommutativeIdealPowers.value C J.
have hPower k:P k `<=` f @^-1` Q k.
  elim:k=>[|k ih];first by rewrite /Q commutative_ideal_power_zeroE.
  rewrite /P commutative_ideal_power_successorE.
  apply:commutative_ideal_product_minimal.
  - exact:(@commutative_ideal_ring_preimage A C f (Q k.+1)
      (@commutative_ideal_power_is_ideal C J k.+1)).
  - move=>a b ha hb;change (Q k.+1 (f (a*b))).
    rewrite rmorphM /Q commutative_ideal_power_successorE.
    exact:(@commutative_ideal_product_contains C J (Q k) (f a) (f b) (hImage a ha) (ih b hb)).
move=>k a ha;exact:hPower k a ha.
Qed.
