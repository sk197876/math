(** Federer (1969), 2.2.16, p. 71: private existence of a maximal strictly
    separated subset, by the general set-theoretic Zorn principle already
    used in the project. Unions of inclusion chains preserve separation; no
    external maximal-net theorem is imported. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import SeparatedMetricSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [maximal_separated_subset_exists]: existence
    of the maximal subsets chosen in Federer 2.2.16,
    p. 71. The empty ambient set is permitted and
    no positivity hypothesis is needed for existence itself. *)
Theorem maximal_separated_subset_exists (R : realType) (X : metricType R)
    (A : set X) (r : R) : exists S, is_maximal_separated_subset A r S.
Proof.
pose P S := S `<=` A /\ is_strictly_separated_metric_set r S.
pose T := {S : set X | P S}.
pose inc (a b : T) := sval a `<=` sval b.
pose rel (a b : T) := `[< inc a b >].
have hrefl a : rel a a by apply/asboolP.
have htrans a b c : rel a b -> rel b c -> rel a c.
  move=> /asboolP hab /asboolP hbc; apply/asboolP=> x hx; exact: hbc (hab x hx).
have hanti a b : rel a b -> rel b a -> a = b.
  move=> /asboolP hab /asboolP hba; case: a hab hba=> a ha; case: b=> b hb hab hba.
  apply: eq_exist; apply/seteqP; by split.
have hchain (F : set T) : total_on F rel -> exists b, forall a, F a -> rel a b.
  move=> hF.
  pose U := \bigcup_(a in F) sval a.
  have hUA : U `<=` A.
    move=> x [a ha hx]; exact: (svalP a).1 hx.
  have hsep : is_strictly_separated_metric_set r U.
    move=> x y [a ha hx] [b hb hy] hxy.
    have [/asboolP hab|/asboolP hba] := hF a b ha hb.
    - exact: (svalP b).2 (hab x hx) hy hxy.
    - exact: (svalP a).2 hx (hba y hy) hxy.
  exists (exist P U (conj hUA hsep))=> a ha; apply/asboolP=> x hx; by exists a.
have [a hmax] := @Zorn T rel hrefl htrans hanti hchain.
exists (sval a); constructor.
- exact: (svalP a).1.
- exact: (svalP a).2.
- move=> S hSA hS hin.
  pose b : T := exist P S (conj hSA hS).
  have hab : rel a b by apply/asboolP.
  have hba := hmax b hab.
  change (sval b `<=` sval a); by rewrite hba.
Qed.
