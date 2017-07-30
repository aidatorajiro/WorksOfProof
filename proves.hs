{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- [定義]
type Not x = (forall a. x -> a)

-- [公理]
-- 排中律
class Classic where
    classic :: Either p (Not p)

-- [証明]
-- 三段論法
syllogism :: (p -> q) -> (q -> r) -> (p -> r)
syllogism h1 h2 = h2 . h1

-- 交換法則（かつ）
commutativeLawAnd :: (p, q) -> (q, p)
commutativeLawAnd (p, q) = (q, p)

-- 交換法則（または）
commutativeLawOr :: Either p q -> Either q p
commutativeLawOr (Left  p) = Right p
commutativeLawOr (Right q) = Left  q

-- 結合法則
associativeLaw :: ((p -> q) -> r) -> (p -> (q -> r))
associativeLaw h = const $ h . const

-- (Pかつ(Pでない))ならばQ
falseBomb :: (p, Not p) -> q
falseBomb (p, np) = np p

-- ド・モルガンの法則
deMorgan :: (Not p, Not q) -> Not (Either p q)
deMorgan (p, _) (Left  r) = p r
deMorgan (_, q) (Right r) = q r

-- 二重否定法則
pnnp :: p -> Not (Not p)
pnnp p np = np p

nnpp :: Classic => Not (Not p) -> p
nnpp nnp = case classic of
    Right np -> nnp np
    Left   p -> p

-- 対偶
contraposition1 :: (p -> q) -> (Not q -> Not p)
contraposition1 h nq = nq . h

--contraposition2 :: (Not q -> Not p) -> (Not (Not p) -> Not (Not q))
--contraposition2 h = contraposition1 h

--x :: Classic => (Not (Not p) -> Not (Not q)) -> (p -> q)
--x h p = nnpp $ h $ pnnp p

--contraposition2 :: (Not q -> Not p) -> (p -> q)
--contraposition2 h p = x $ contraposition_dn h

-- なんか
prop1 :: (forall p. ((p -> q) -> q)) -> ((p -> q) -> p) -> p
prop1 h h0 = h0 $ const $ h id

main :: IO ()
main = return ()