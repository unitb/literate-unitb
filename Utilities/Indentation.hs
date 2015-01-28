{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
module Utilities.Indentation where

-- import Control.Applicative
import Control.Lens
import Control.Monad.Reader
-- import Control.Monad.Reader.Class

import Data.Proxy

class MonadReader r m => Indentation r m | m -> r where
    _margin :: Proxy m -> Lens' r Int
    margin :: m Int
    indent :: Int -> m a -> m a
    mk_lines :: String -> m [String]
    margin_string :: m String

    margin = asks $ view (_margin (Proxy :: Proxy m))
    indent n cmd = local (over (_margin (Proxy :: Proxy m)) (n+)) cmd
    mk_lines "" = return [""]
    mk_lines xs = do
        m <- margin_string
        return $ map (m ++) $ lines xs
    margin_string = do
        n <- margin 
        return $ replicate n ' '

instance Indentation Int (Reader Int) where
    _margin = (\_ -> id)

