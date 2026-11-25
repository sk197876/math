(** Federer (1969), 3.2.28(3), printed pp. 265–266:
    a point in a forgetful-map fibre is specified by its
    restriction to im alpha and its value on the last
    adapted unit normal. Existence is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_euclidean_frame_extension]: the exact
    fibre data for S(g)=g alpha in Federer 3.2.28(3),
    pp. 265–266. These laws specify a linear map
    by its restriction and its last adapted vector;
    they do not postulate an extension. *)
Record is_euclidean_frame_extension (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1)) (w:R_n R k.+1)
    (beta:Hom (R_n R k) (R_n R n)) (v:R_n R n)
    (h:Hom (R_n R k.+1) (R_n R n)):Prop:={
  (** Source for [frame_extension_restriction]: h alpha=beta
      is the actual fibre equation in Federer
      3.2.28(3), p. 266. *)
  frame_extension_restriction:hom_comp h alpha=beta;
  (** Source for [frame_extension_normal_value]: h(e_m)=v
      is the remaining fibre parameter in Federer
      3.2.28(3), p. 266. *)
  frame_extension_normal_value:h w=v
}.
