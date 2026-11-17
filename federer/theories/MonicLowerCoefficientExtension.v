(** Federer (1969), 3.4.8(10), pp. 331–332:
    connect the original leading-one polynomial
    to the project's finite coefficient root
    theorem. Append its actual leading coefficient;
    do not change the degree or lower coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [monic_lower_coefficient_extension]:
    the original first equation is monic
    of degree k, 3.4.8(10),
    pp. 331–332. This supporting connection
    exposes its full finite coefficient vector,
    including the degree-zero case. *)
Theorem monic_lower_coefficient_extension (R:realType) k (b:'I_k->R):
  exists c:'I_k.+1->R,c ord_max = 1 /\
    (forall i:'I_k,c (widen_ord (leqnSn k) i) = b i) /\
    forall t:R,\sum_(i<k.+1) c i*t^+(i:nat) = t^+k+\sum_(i<k) b i*t^+(i:nat).
Proof.
pose s:=rcons (map b (enum 'I_k)) 1.
pose c:=fun i:'I_k.+1=>nth 0 s (i:nat).
have hLeading:c ord_max = 1 by rewrite /c /s nth_rcons size_map size_enum_ord ltnn eqxx.
have hLower (i:'I_k):c (widen_ord (leqnSn k) i) = b i.
  rewrite /c /s nth_rcons size_map size_enum_ord /= ltn_ord.
  by rewrite (nth_map i) ?size_enum_ord ?ltn_ord // nth_ord_enum.
exists c;split;first exact:hLeading.
split;first exact:hLower.
move=>t;rewrite big_ord_recr hLeading mul1r addrC.
congr (_+_);apply:eq_bigr=>i _;by rewrite hLower.
Qed.
