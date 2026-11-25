(** Federer (1969), 4.1.6, p. 355: products
    of closed coordinate one-form fields are closed.
    This is the original generator argument, proved
    with the existing ordered product and the actual
    original derivative and induced form norms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom InnerNorm EuclideanInnerProduct GrassmannAbbreviations
  NormDifferentialUP Alternating AlternatingProduct OneFormProducts ScalarCoefficients
  OneFormProductHead RealDifferentialFormCalculus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [closed_real_one_form_products]: closure
    under multiplication used in the coordinate-generator
    proof of Federer 4.1.6, p. 355.
    The empty product and dimension zero are retained. *)
Theorem closed_real_one_form_products (R:realType) (h2:(1+1:R)!=0) n m
    (U:R_n R n->Prop) (forms:'I_m->R_n R n->A_m (R_n R n) R^o 1) a:
  norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U a->
  (forall i,has_real_form_derivative h2 U (forms i) a 0)->
  has_real_form_derivative h2 U
    (fun x=>one_forms_wedge h2 (scalar_bilinear R) 1 (fun i=>forms i x)) a 0.
Proof.
move=>hInterior; elim:m forms=>[|m ih] forms hAll.
- have hFunction:(fun x=>one_forms_wedge h2 (scalar_bilinear R) 1 (fun i=>forms i x))=
      (fun _ : R_n R n=>@zero_form R (R_n R n) R^o 1).
    apply:funext=>x; exact:original_one_forms_wedge_empty.
  rewrite hFunction; exact:constant_real_form_closed.
- have hFunction:(fun x=>one_forms_wedge h2 (scalar_bilinear R) 1 (fun i=>forms i x))=
      (fun x=>form_wedge h2 (scalar_bilinear R) (forms ord0 x)
        (one_forms_wedge h2 (scalar_bilinear R) 1 (fun i:'I_m=>forms (lift ord0 i) x))).
    apply:funext=>x; exact:original_one_forms_wedge_head.
  rewrite hFunction.
  apply:(@closed_real_forms_product_closed R h2 n 1 m U (forms ord0)
    (fun x=>one_forms_wedge h2 (scalar_bilinear R) 1 (fun i:'I_m=>forms (lift ord0 i) x)) a).
  + exact:hAll.
  + apply:ih=>i; exact:hAll.
Qed.
