(** Federer (1969), 2.6.4, p. 118: algebraic part of the map sending f,g to
    the function (x,y) |-> f(x)g(y). The proof is independent of measures
    and applies to arbitrary linear function representations. The universal
    property used here is Federer 1.1.1, p. 9 *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import TensorUP TensorProduct TensorSpan.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Product.
Variable K : fieldType.
Variables X Y : Type.
Variables U V : lmodType K.
Variables (u : {linear U -> (X -> K^o)}) (v : {linear V -> (Y -> K^o)}).

(** Source for [function_product_pair]: the separated-variable
    product formula in Federer 2.6.4, p. 118, abstracted
    from the later summable-function instance. *)
Definition function_product_pair (f : U) (g : V) (p : X*Y) := u f p.1 * v g p.2.

(** Source for [function_product_pair_bilinear]: bilinearity of
    the first map in Federer 2.6.4, p. 118. This
    algebraic assertion requires no integrability hypothesis. *)
Lemma function_product_pair_bilinear : bilinear function_product_pair.
Proof.
split.
- move=> g c f h; apply: funext=> p; case: p=> x y.
  rewrite /function_product_pair /= (linearP u) !fctE /=.
  change ((c*u f x+u h x)*v g y = c*(u f x*v g y)+u h x*v g y).
  by rewrite mulrDl mulrA.
- move=> f c g h; apply: funext=> p; case: p=> x y.
  rewrite /function_product_pair /= (linearP v) !fctE /=.
  change (u f x*(c*v g y+v h y) = c*(u f x*v g y)+u f x*v h y).
  by rewrite mulrDr mulrCA.
Qed.

(** Source for [function_tensor_map]: the induced linear map
    in Federer 2.6.4, p. 118, via the abstract universal
    property 1.1.1, p. 9. Here the target is the full
    function space; summability and injectivity are proved separately. *)
Definition function_tensor_map : {linear tensor_space U V -> ((X*Y) -> K^o)} :=
  GRing.Linear.clone _ _ _ _ (tensor_lift function_product_pair_bilinear) _.

(** Source for [function_tensor_map_generator]: the defining
    product formula of the induced map in Federer 2.6.4,
    p. 118, on pure tensors. *)
Lemma function_tensor_map_generator f g p :
  function_tensor_map (tensor_inj f g) p = u f p.1 * v g p.2.
Proof. change (tensor_lift function_product_pair_bilinear (tensor_inj f g) p = u f p.1 * v g p.2).
by rewrite tensor_liftE. Qed.
End Product.
