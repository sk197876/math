(** Federer (1969), 4.1.27, p. 384:
    the original prefix-product parametrisation of
    an ordered simplex by the open
    unit cube, its exact image, injectivity,
    differential wedge, actual current image and
    Hausdorff-density representation. Nondegenerate orientation,
    degenerate zero currents and degree zero
    retain their separate original interpretations.
    The printed affine-plane hypothesis of univalence
    is used literally whenever m<=n+1; its vacuous case
    n+1<m has an actual counterexample. *)
From Federer Require Export SimplexCubeParametrisationUP
  SimplexCubeParametrisationExistence SimplexCubeParametrisationSealed
  SimplexCubeExactImage SimplexCubeInjectivity SimplexCubeParametrisationClass
  SimplexCubeJacobian SimplexConsecutiveOrientation SimplexCubeNormalisedDifferential
  SimplexCubeSourceCurrent SimplexCubeProductCurrent SimplexCubeCurrentImage
  SimplexHausdorffDensityUP SimplexHausdorffDensityExistence SimplexHausdorffDensitySealed
  SimplexHausdorffCurrent SimplexCubeDegeneracy SimplexHausdorffCurrentAllVertices
  SimplexAffinePlaneUnivalence.
