(** Public laws for Federer (1969), 4.1.16, pp. 373–374:
    the original closed-convex nearest-point relation, its
    nonexpanding opaque map and printed segment argument,
    and flat-current support on the precise compact convex
    hull with exact compact-index norm equality. Closed C
    in the projection assertion may be unbounded. Empty
    support in the current assertion remains allowed. *)
From Federer Require Export EuclideanConvexNearestMapUP
  EuclideanConvexNearestMapExistence EuclideanConvexNearestMapSealed
  EuclideanConvexNearestMapLaws EuclideanConvexNearestMapQuadratic
  EuclideanConvexNearestMapOwnNorm EuclideanCompactConvexHullAll
  EuclideanCompactNearestMap EuclideanFlatConvexHullIndex
  FlatCurrentNonexpandingPushforward EuclideanFlatConvexHull.
