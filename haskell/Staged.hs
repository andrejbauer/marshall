{- | A staged computation is a sequence of approximations which represents its limit. Specifically,
  we think of modeling a topological space as a subspace of a continuous domain with a countable
  base, for theoretical background see the paper http://dx.doi.org/10.1016/j.apal.2008.09.025 (also
  available at http://math.andrej.com/)

  Suppose we would like to represent a space X, where X is some sort of a complete space (either
  metrically or domain-theoretically complete). We think of the points of X as limits of sequences
  of approximations. For example, a real number may be thought of as a sequence of intervals which
  all contain x and whose widths converge to 0. In the general case the approximations can be
  abstract entities that need not correspond to intervals (although each approximation naturally
  corresponds to the subset of those points that it approximates.) The approximations are naturally
  order by how well they approximate the values (for intervals this is reverse inclusion) and they form
  a /base/ for a continuous domain, see the cited paper above.

  If @b@ ("b" for the "base") is the datatype which represents the approximations, then the elements
  of the space could be represented by the datatype @Int -> b@. However, in practice we need to
  control the direction of approximation: a real number may be rounded up or down, a set may be
  approximated from inside or from outside, etc. Thus we include rounding information in the
  sequence, so that an element of the space is represented by the datatype @'Stage' -> b@ where
  'Stage' carries rounding information and the index.

  We empahsize that the rounding mode is /not/ that of floating point arithmetic. Rather, it tells
  us whether the exact results should be approximated from below or above in the natural order of
  approximations. Typically, computations based on domain-theoretic models always approximate from
  below, but there are uses for over-approximations as well, for example when we estimate the truth
  value of a quantifier. Therefore we allow approximating sequences which approach their limit from
  above in the domai-theoretic order.

  It is cumbersome to work with the datatype @Stage -> b@ explicitly because we need to manually pass
  around the @Stage@ parameter. Haskell comes in handy here, as we define a monad which is very much
  like the @Reader@ monad of Haskell.
-}

module Staged where

-- | The rounding mode tells us whether we should under- or over-approximate the exact result.
data RoundingMode = RoundUp | RoundDown
                  deriving (Eq, Show)

-- | A stage of computation tells us how hard we should try to compute the result. The 'stage' component
-- is a measure of precisions. As it goes to infinity, the approximation should converge to the exact
-- value (in the sense of Scott topology on the underlying domain model).
data Stage = Stage { precision :: Int, rounding :: RoundingMode }
             deriving Show

-- | 'anti' reverses the rounding mode
anti :: Stage -> Stage
anti s = Stage {precision = precision s, rounding = case rounding s of { RoundUp -> RoundDown ; RoundDown -> RoundUp}}

-- | @prec_down k@ sets precision to @k@ and the rounding mode to 'RoundDown'
prec_down :: Int -> Stage
prec_down k = Stage {precision = k, rounding = RoundDown}

-- | @prec_up k@ sets precision to @k@ and the rounding mode to 'RoundUp'
prec_up :: Int -> Stage
prec_up k = Stage {precision = k, rounding = RoundUp}

-- | @prec r k@ is the stage with given rounding @r@ and precision @k@
prec :: RoundingMode -> Int -> Stage
prec r k = Stage {precision = k, rounding = r}

{- | The 'Completion' class represents a completion operation. An instance @m@ of class 'Completion'
   is a type constructor which takes a type @b@ representing the base, i.e., the approximations, and
   gives the type @m b@ of the completion of @b@. For example, if @b@ is the datatype of dyadic
   intervals, then @m b@ would be the interval domain.

   Each element of the completion @m b@ may be converted to a sequence of approximations with the
   "approximate" function. Conversely, a sequence of approximations may be converted to the element
   with the "limit" function.
-}

class (Functor m, Monad m) => Completion m where
    get_stage :: m Stage -- ^ get the current stage
    get_rounding :: m RoundingMode -- ^ get the current rounding
    get_prec :: m Int -- ^ get the current precision
    approximate :: m t -> (Stage -> t) -- ^ approximate by a chain (from above or from below, depending on rounding mode)
    limit :: (Stage -> t) -> m t -- ^ the element represented by a given chain

    embed :: t -> m t -- ^ a synonym for @return@
    embed = return

    -- | lift a map from approximations to points
    lift1 :: (Stage -> t -> u) -> m t -> m u
    lift1 f x = do a <- x
                   s <- get_stage
                   return $ f s a

    -- | lift a map of two arguments from approximations to points.
    lift2 :: (Stage -> t -> u -> v) -> m t -> m u -> m v
    lift2 f x y = do a <- x
                     b <- y
                     s <- get_stage
                     return $ f s a b

-- | If @t@ is the type of approximations then, @Staged t@ is the type of the points of the space,
-- represented as sequences of approximations.
newtype Staged t = Staged { approx :: Stage -> t }

-- | The monad structure of 'Staged' is the same as that of the @Reader@ monad.
instance Monad Staged where
  return x = Staged $ \s -> x
  x >>= f  = Staged $ \s -> approx (f (approx x s)) s

-- | The functor structure of 'Staged' is the same as that of the @Reader@ monad.
instance Functor Staged where
  fmap f x = Staged $ \s -> f (approx x s)

-- | 'Staged' is an instance of a completion.
instance Completion Staged where
    get_stage = Staged $ \s -> s
    get_rounding = Staged $ rounding
    get_prec = Staged $ precision
    approximate = approx
    limit = Staged