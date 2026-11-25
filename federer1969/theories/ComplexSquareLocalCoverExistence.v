(** Federer (1969), 3.4.12, p. 339: prove the actual
    square-map local double cover. The existing inverse theorem
    supplies one holomorphic root; its negative is the second.
    Original root classification proves disjointness and exhaustion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import TensorFamilyBinary Hom RealNormUP NormMetric NormMetricScaleContinuity
  ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormDifferentialUP NormBoundedLinearTopology NormDiffeomorphismUP
  NormAnalyticLocal HolomorphicUP HolomorphicRestriction HolomorphicNegation
  ComplexSquareRoots ComplexSquareCoverObstruction ComplexSquareLocalInverse ComplexSquareLocalCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Cover.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
Local Notation M:=(real_norm_metric_space hN).
Local Notation puncture:=([set z:M|z<>0]).

(** Source for [original_complex_square_local_cover_exists]:
    every nonzero original base point has exactly two local
    holomorphic sheets, as required in the complex replacement
    of 3.4.8(10), 3.4.12, p. 339. The branch images
    are relatively open and every original fibre is exhausted. *)
Theorem original_complex_square_local_cover_exists (w:C):w<>0 ->
  exists W:set M,exists s:'I_2->C->C,is_original_complex_square_local_cover w W s.
Proof.
move=>hWNonzero.
have [a [hA [hDifferent [hRoot hRoots]]]]:=@original_complex_nonzero_square_roots R w hWNonzero.
have [r [hR [g [hInverse hG]]]]:=@complex_square_nonzero_local_inverse R a hA.
pose B:set M:=[set x|N (x-a)<r].
pose V:set M:=(fun z:C=>z^+2) @` B.
have hBOpen:@open M B:=norm_diffeomorphism_source_open hInverse.
have hVOpen:@open M V:=norm_diffeomorphism_target_open hInverse.
have hAIn:B a by change (is_true (N (a-a)<r));rewrite subrr (real_seminorm_zero hN.1).
have hWIn:V w by exists a;first exact:hAIn;exact:hRoot.
have hPuncture:@open M puncture.
  have hSame:puncture=~` [set (0:C)] by apply:funext=>z;by [].
  rewrite hSame;apply:closed_openC;apply:accessible_closed_set1;
  apply:hausdorff_accessible;exact:metric_hausdorff.
pose W:set M:=V `&` puncture.
have hOpenW:@open M W:=openI hVOpen hPuncture.
have hCentre:W w by split.
have hInterior v (hv:W v):@norm_domain_interior R CR N W v.
  apply:(@norm_domain_interior_neighbourhood R CR N hN W v).2.
  have h:=hOpenW;rewrite openE in h;exact:h v hv.
have hGW:@is_holomorphic R C^o C^o N N hN hN W g.
  exact:(@holomorphic_open_restriction R C^o C^o N N hN hN V W g
    (fun v hv=>hv.1) hInterior hG).
have hSquare v (hv:W v):(g v)^+2=v:=norm_diffeomorphism_right_inverse hInverse hv.1.
have hNonzero v (hv:W v):g v<>0.
  move=>hZero;apply:hv.2;by rewrite -(hSquare v hv) hZero expr0n.
have hOpposite v (hv:W v):g v<> -g v.
  have [z [hZ [hDistinct [hZSquare hClassify]]]]:=@original_complex_nonzero_square_roots R v hv.2.
  have [hFirst|hSecond]:=(hClassify (g v)).1 (hSquare v hv).
  - by rewrite hFirst.
  - rewrite hSecond;move=>hEqual;apply:hDistinct.
    by rewrite opprK in hEqual;exact:esym hEqual.
have hNegContinuous:continuous (fun z:M=>(-z:M)).
  have hSame:(fun z:M=>-z)=(fun z:M=>(-1:R)*:(z:CR))
    by apply:funext=>z;rewrite scaleN1r.
  rewrite hSame;exact:real_norm_metric_scale_continuous.
pose O:set M:=B `&` ((fun z:C=>z^+2) @^-1` W).
have hOOpen:@open M O.
  apply:openI hBOpen _.
  exact:(@open_comp M M (fun z:C=>z^+2) W (fun z _=>@complex_square_map_continuous R z) hOpenW).
have hImage:g @` W=puncture `&` O.
  apply/seteqP;split.
  - move=>z [v hv <-];split;first exact:hNonzero v hv.
    split;first exact:(@norm_diffeomorphism_inverse_maps R CR CR N N hN hN B V
      (fun q:C=>q^+2) g 1%N hInverse v hv.1).
    by change (W ((g v)^+2));rewrite hSquare.
  - move=>z [hz [hzB hzW]];exists (z^+2);first exact:hzW.
    exact:(@norm_diffeomorphism_left_inverse R CR CR N N hN hN B V
      (fun q:C=>q^+2) g 1%N hInverse z hzB).
have hNegImage:(fun v:C=> -g v) @` W=puncture `&` ((fun z:C=> -z) @^-1` O).
  apply/seteqP;split.
  - move=>z [v hv <-];split.
    + move=>hZero;apply:(hNonzero v hv);have h:=congr1 (fun q:C=> -q) hZero.
      by rewrite opprK oppr0 in h.
    + change (O (- -g v));rewrite opprK.
      have h:(puncture `&` O) (g v) by rewrite -hImage;exists v.
      exact:h.2.
  - move=>z [hz hzO].
    have hzNeg:(-z:C)<>0 by move=>hZero;apply:hz;have h:=congr1 (fun q:C=> -q) hZero;by rewrite opprK oppr0 in h.
    have [v hv hValue]:(g @` W) (-z) by rewrite hImage;split.
    exists v;first exact:hv.
    by rewrite hValue opprK.
pose s:=fun (i:'I_2) v=>if i==ord0 then g v else -g v.
exists W,s;split;first exact:hOpenW.
split;first exact:hCentre.
split;first by move=>v hv;exact:hv.2.
split.
- elim/ord2_rect;rewrite /s /=;[exact:hGW|exact:holomorphic_negate hGW].
split.
- elim/ord2_rect=>v hv;rewrite /s /=;first exact:hSquare v hv.
  by rewrite expr2 mulNr mulrN opprK -expr2 hSquare.
split.
- elim/ord2_rect;elim/ord2_rect=>v hv hEqual;try reflexivity.
  + exfalso;exact:(hOpposite v hv hEqual).
  + exfalso;exact:(hOpposite v hv (esym hEqual)).
split.
- move=>z hzW.
  have [u [hU [hDifferentU [hUSquare hClassify]]]]:=@original_complex_nonzero_square_roots R (z^+2) hzW.2.
  have [hGFirst|hGSecond]:=(hClassify (g (z^+2))).1 (hSquare (z^+2) hzW);
    have [hZFirst|hZSecond]:=(hClassify z).1 (erefl _).
  + exists ord0;by rewrite /s /= hGFirst hZFirst.
  + exists ord1;by rewrite /s /= hGFirst hZSecond.
  + exists ord1;by rewrite /s /= hGSecond hZFirst opprK.
  + exists ord0;by rewrite /s /= hGSecond hZSecond.
- elim/ord2_rect;rewrite /s /=.
  + exists O;by split.
  + exists ((fun z:C=> -z) @^-1` O);split;last exact:hNegImage.
    exact:(@open_comp M M (fun z:C=> -z) O (fun z _=>hNegContinuous z) hOOpen).
Qed.
End Cover.
