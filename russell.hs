newtype Set x = Set (Set x -> Bool)

unSet :: Set x -> (Set x -> Bool)
unSet (Set x) = x

isElement :: Set x -> Set x -> Bool
isElement (Set f) = f

russell :: Set x
russell = Set (\(Set f) -> not $ f (Set f))

main :: IO ()
main = print $ isElement russell russell
