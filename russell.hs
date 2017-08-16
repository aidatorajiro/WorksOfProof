newtype Set x = Set (Set x -> Bool)

unSet :: Set x -> (Set x -> Bool)
unSet (Set x) = x

russell :: Set x
russell = Set (\(Set f) -> not $ f (Set f))

main :: IO ()
main = print $ unSet russell russell
