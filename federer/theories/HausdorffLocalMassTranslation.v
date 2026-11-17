(** Federer (1969), 3.4.10, p. 337:
    translate a local Hausdorff mass bound back
    to its original centre. The set need
    not be analytic. Reuse the project's proved
    invariance under an isometric bijection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric NormClosureLaws GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [hausdorff_local_mass_translation]: the
    change of centre in the compact-mass assertions
    of 3.4.10, p. 337. The
    original set and measure degree are retained;
    no local analyticity is needed for this connection. *)
Theorem hausdorff_local_mass_translation (R:realType) n
    (A:set (R_n R n)) (a:R_n R n) k:
  let hB:=@euclidean_inner_productP R n in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  (exists O:set (R_n R n),@open T O /\O 0 /\
    (@hausdorff_measure R (inner_metric_space hB) k
      ([set x:R_n R n|A ((a+x)%R)] `&` O)< +oo)%E) ->
  exists W:set (R_n R n),@open T W /\W a /\
    (@hausdorff_measure R (inner_metric_space hB) k (A `&` W)< +oo)%E.
Proof.
move=>hB hNX T [O [hO [hO0 hMass]]].
pose E:=inner_metric_space hB.
pose u:=fun x:T=>(a+x:T).
pose v:=fun x:T=>(x-a:T).
have hV:continuous v.
  have hSame:v=(fun x:T=>(-a+x:T)) by apply:funext=>x;rewrite /v addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hVU:cancel u v by move=>x;rewrite /u /v addrAC subrr add0r.
have hUV:cancel v u by move=>x;rewrite /u /v addrC subrK.
exists (v @^-1` O);split.
- exact:(@open_comp T T v O (fun x _=>hV x) hO).
split;first by change (O (a-a));rewrite subrr.
have hDistance (x y:E):@mdist R E (u x) (u y)=@mdist R E x y.
  rewrite !inner_metric_distanceE.
  by rewrite /u opprD addrACA subrr add0r.
have hImage:u @` ([set x|A (a+x)] `&` O)=A `&` (v @^-1` O).
  apply/seteqP;split.
  + move=>x [y [hyA hyO] <-];split;first exact:hyA.
    by change (O (v (u y)));rewrite hVU.
  + move=>x [hxA hxO];exists (v x);last exact:hUV x.
    split;last exact:hxO;by change (A (u (v x)));rewrite hUV.
rewrite -hImage (@hausdorff_bijective_isometry_invariance R E E u v hVU hUV hDistance).
exact:hMass.
Qed.
