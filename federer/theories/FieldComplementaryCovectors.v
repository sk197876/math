(** Federer (1969), 3.4.12, p. 339, extending functional
    submanifolds in 3.4.5, p. 321: complete the actual independent
    equation covectors to local source coordinates. Reuse basis
    extension, equality of basis sizes, and the original dual basis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Annihilator Hom Bilinear FiniteCoordinates LinearBasis FiniteIndependence FiniteBasisExtension
  FiniteBasisComparison FiniteDualDimension OrdinalCoordinateTail FieldPrefixSuffixSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
(** Source for [field_complementary_covectors]: the original
    independent equation differentials admit complementary coordinate
    covectors, supporting functional holomorphic charts in 3.4.12,
    p. 339. This is the missing connection between the
    existing basis extension and the existing joint inverse theorem. *)
Theorem field_complementary_covectors (K:fieldType) (X:lmodType K) n m
    (e:'I_n->X) (he:is_basis e) (hMN:(m<=n)%N)
    (D:'I_(n-m)->Hom X K^o):finite_independent D ->
  exists P:Hom X (coordinate_space K m),
    forall x,P x = 0 ->(forall j,D j x = 0) ->x = 0.
Proof.
move=>hD.
have [r [hQR [lambda [hLambda hFirst]]]]:=@finite_basis_extension K (Hom X K^o)
  (n-m) D hD n (dual_basis he) (dual_basisP he).
have hSize:r = n:=@finite_basis_size K (Hom X K^o) r n lambda (dual_basis he) hLambda (dual_basisP he).
subst r.
have hTailSize:(n-(n-m))%N = m by rewrite subKn.
pose index:=fun j:'I_m=>ordinal_coordinate_tail_index hQR (cast_ord (esym hTailSize) j).
pose p:=fun x:X=>[ffun j:'I_m=>lambda (index j) x].
have hLinear:linear p.
  move=>c x y;apply/ffunP=>j;rewrite /p !ffunE;exact:hom_linear.
pose P:=@HomMap K X (coordinate_space K m) p (introT (asboolP _) hLinear).
exists P=>x hP hZero.
have hAll i:lambda i x = 0.
  case:(ltnP (i:nat) (n-m))=>hSmall.
  - pose j:'I_(n-m):=Ordinal hSmall.
    have hIndex:widen_ord hQR j = i by apply:val_inj.
    rewrite -hIndex hFirst;exact:hZero j.
  - have [j hIndex]:=@ordinal_coordinate_tail_complete n (n-m) hQR i hSmall.
    have h:=congr1 (fun y:coordinate_space K m=>y (cast_ord hTailSize j)) hP.
    have hCast:cast_ord (esym hTailSize) (cast_ord hTailSize j) = j by apply:val_inj.
    change (p x (cast_ord hTailSize j) = (0:coordinate_space K m) (cast_ord hTailSize j)) in h.
    by rewrite /p !ffunE /index hCast hIndex in h.
have hEvery L:(L:Hom X K^o) x = 0.
  apply:(@basis_induction K (Choice.clone 'I_n _) (Hom X K^o) lambda hLambda
    (fun L=>L x = 0)).
  - exact:hom_zeroE.
  - move=>L1 L2 hL1 hL2;by rewrite hom_addE hL1 hL2 addr0.
  - move=>c L1 hL1;by rewrite hom_scaleE hL1 scaler0.
  - exact:hAll.
rewrite {1}(basis_vector_expansion he x).
apply:big1=>i _;by rewrite hEvery scale0r.
Qed.
