import Data.Tuple
import Control.Arrow

split :: [a] -> ([a], [a])
split []     = ([], [])
split (x:xs) = first (x:) . swap $ split xs

merge :: Ord a => (a -> a -> Ordering) -> ([a], [a]) -> [a]
merge _ (xxs, []) = xxs
merge _ ([], yys) = yys
merge cmp (x:xs, y:ys) =
    case cmp y x of
      LT -> y : merge cmp (x:xs, ys)
      _  -> x : merge cmp (xs, y:ys)

mergesort :: Ord a => (a -> a -> Ordering) -> [a] -> [a]
mergesort _   []  = []
mergesort _   [x] = [x]
mergesort cmp xxs = merge cmp $ mergesort cmp *** mergesort cmp $ split xxs
