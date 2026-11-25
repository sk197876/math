(** Federer (1969), 3.4.8(11), p. 335:
    restrict the original projection to the
    base ball outside the additional analytic zero set.
    Its component images follow from the actual
    component homeomorphisms of (10), without repeating
    the finite-sheet or inverse-function arguments. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import MetricSubsetBackground HomeomorphismUP OpenSubsetContinuousExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [component_homeomorphism_restriction_image]:
    the original restricted T projects componentwise
    onto the corresponding base components,
    3.4.8(11), p. 335. Openness of
    the original base components is supplied by
    the project's normed-space component theorem. *)
Theorem component_homeomorphism_restriction_image (R:realType) (X Y:metricType R)
    (P:X->Y) (Z:set X) (V W:set Y):
  continuous P ->W `<=` V ->
  (forall y,V y ->open (connected_component V y)) ->
  (forall x,Z x ->exists F:metric_subset (connected_component Z x)->
      metric_subset (connected_component V (P x)),
    (forall a,val (F a) = P (val a)) /\is_homeomorphism F) ->
  forall x,Z x ->W (P x) ->
    P @` connected_component (Z `&` (P @^-1` W)) x = connected_component W (P x).
Proof.
move=>hP hWV hOpenComponents hHomeomorphisms x hZx hWx.
pose D:set X:=Z `&` (P @^-1` W).
pose C:=connected_component Z x.
pose B:=connected_component V (P x).
pose K:=connected_component W (P x).
have hDx:D x by split.
have hKP:K (P x):=connected_component_refl hWx.
have hKW:K `<=` W:=@connected_component_sub Y W (P x).
have hKB:K `<=` B.
  apply:(@connected_component_max Y V K (P x) hKP _ (@component_connected Y W (P x))).
  move=>y hy;exact:hWV y (hKW y hy).
have [F [hForward [G hInverse]]]:=hHomeomorphisms x hZx.
have hBOpen:open B:=hOpenComponents (P x) (hWV (P x) hWx).
have hGContinuous:continuous (fun b:metric_subset B=>(val (G b):X)).
  move=>b W0 hW0.
  have hNear:nbhs (G b) [set a:metric_subset C|W0 (val a)].
    exact:(@metric_subset_inclusion_continuous R X C (G b) W0 hW0).
  have hBack:=@homeomorphism_inverse_continuous (metric_subset C) (metric_subset B)
    F G hInverse b _ hNear.
  exact:hBack.
have [psi [hPsi hPsiContinuous]]:=@open_subset_continuous_extension_exists R X Y B
  (fun b:metric_subset B=>(val (G b):X)) x hBOpen hGContinuous.
have hRange y (hy:B y):C (psi y) /\ P (psi y) = y.
  pose b:metric_subset B:=exist _ y (mem_set hy).
  have hPsiB:psi y = val (G b):=hPsi b.
  split.
  - rewrite hPsiB;exact:set_valP (G b).
  - have hEquality:=congr1 val (homeomorphism_right_inverse hInverse b).
    rewrite hForward in hEquality.
    by rewrite hPsiB.
have hPsiBase:psi (P x) = x.
  pose a:metric_subset C:=exist _ x (mem_set (connected_component_refl hZx)).
  have hEquality:psi (val (F a)) = x.
    rewrite hPsi (homeomorphism_left_inverse hInverse a);by [].
  by rewrite hForward in hEquality.
have hPsiK:{within K,continuous psi}.
  apply:continuous_in_subspaceT=>y /asboolP hy;exact:hPsiContinuous y (hKB y hy).
have hConnectedImage:connected (psi @` K):=
  connected_continuous_connected (@component_connected Y W (P x)) hPsiK.
have hImageInside:(psi @` K) `<=` D.
  move=>z [y hy <-];have [hCy hPy]:=hRange y (hKB y hy).
  split;first exact:(@connected_component_sub X Z x (psi y) hCy).
  change (W (P (psi y)));rewrite hPy;exact:hKW y hy.
have hImageBase:(psi @` K) x.
  exists (P x);[exact:hKP|exact:hPsiBase].
have hImageComponent:(psi @` K) `<=` connected_component D x:=
  @connected_component_max X D (psi @` K) x hImageBase hImageInside hConnectedImage.
have hProjectedConnected:connected (P @` connected_component D x):=
  connected_continuous_connected (@component_connected X D x) (continuous_subspaceT hP).
have hProjectedInside:(P @` connected_component D x) `<=` W.
  move=>y [z hz <-];exact:(@connected_component_sub X D x z hz).2.
have hProjectedBase:(P @` connected_component D x) (P x).
  exists x;first exact:connected_component_refl hDx.
  by [].
have hProjectedK:(P @` connected_component D x) `<=` K:=
  @connected_component_max Y W (P @` connected_component D x) (P x)
    hProjectedBase hProjectedInside hProjectedConnected.
apply/seteqP;split;first exact:hProjectedK.
move=>y hy;exists (psi y).
- apply:hImageComponent;by exists y.
- exact:(hRange y (hKB y hy)).2.
Qed.
