{-# LANGUAGE ExistentialQuantification,
             ScopedTypeVariables,
             FlexibleInstances,
             CPP  #-}

-- | This module contains the additional data types, instance definitions and functions to run parsers in an interleaved way.
--   If all the interleaved parsers recognise a single connected piece of the input text this incorporates the permutation parsers.
--   For some examples see the module "Text.ParserCombinators.UU.Demo.MergeAndPermute".

module Control.Applicative.Interleaved   
(   -- * Classes
    Splittable (..),
    -- * Types
    Gram (..),
    Alt (..),
    -- * Functions
    mkG,
    mkP,
    (<<||>),
    (<||>),
    sepBy,
    gmList,
   -- * Modules
    module Control.Applicative,
    module Data.Monoid
  ) where

-- import Text.ParserCombinators.UU.Core
import Control.Applicative
import Data.Semigroup as Sem
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 710
import Data.Monoid hiding (Alt)
#else
import Data.Monoid
#endif

infixl 4  <||>
infixl 4  <<||> 

-- * The data type `Gram`
-- | Since we want to get access to the individual parsers which recognise a consecutive 
--   piece of the input text we define a new data type, which lifts the underlying parsers 
--   to the grammatical level, so they can be transformed, manipulated, and run in a piecewise way.
--   `Gram` is defined in such a way that we can always access the first parsers to be ran from such a structure.
--   We require that all the `Alt`s do not recognise the empty string.
--   These should be covered by the `Maybe` in the `Gram` constructor.

data Gram f a =             Gram   [Alt f a]    (Maybe a) 
data Alt  f a =  forall b . Seq    (f (b -> a)) (Gram f b) 
              |  forall b.  Bind   (f b)        (b -> Gram f a)

-- * The requirement that we can split of a possible empty part
class Splittable f where
  getNonPure    :: f a  -> Maybe (f  a)       
  getPure       :: f a  -> Maybe     a

-- * Grammars can be used as a monoid using the <||> combinator to combine them and (.) for composing  results
-- Split up into Monoid + Semigroup for GHC 8.4, see
-- <https://prime.haskell.org/wiki/Libraries/Proposals/SemigroupMonoid#Writingcompatiblecode>
instance Functor f => Sem.Semigroup (Gram f (r -> r)) where
  p <> q = (.) <$> p <||> q

instance Functor f => Monoid (Gram f (r -> r)) where
  mempty      = empty
#if !(MIN_VERSION_base(4,11,0))
  -- this is redundant starting with base-4.11 / GHC 8.4
  -- if you want to avoid CPP, you can define `mappend = (<>)` unconditionally
  mappend = (<>)
#endif

instance (Show a) => Show (Gram f a) where
  show (Gram l ma) = "Gram " ++ show  (length l) ++ " " ++ show ma 

-- | The function `mkGram` splits a simple parser into the possibly empty part and the non-empty part.
--   The non-empty part recognises a consecutive part of the input.
--   Here we use the functions `getOneP` and `getZeroP` which are provided in the uu-parsinglib package,
--   but they could easily be provided by other packages too.



mkG::  (Splittable f, Functor f) => f a -> Gram f a
mkG p =  Gram   (maybe [] (\p -> [(const <$> p) `Seq` pure ()]) (getNonPure p)) 
                (getPure p)


-- * Class instances for Gram
-- | We define instances for the data type `Gram` for `Functor`, `Applicative`,  `Alternative` and `ExtAlternative`
instance Functor f => Functor (Gram f) where
  fmap f (Gram alts e) = Gram (map (f <$>) alts) (f <$> e)

instance Functor f => Functor (Alt f) where
  fmap a2c (fb2a `Seq`  gb)   = ((a2c.) <$> fb2a) `Seq`  gb
  fmap a2c (fb   `Bind` b2ga) = fb                `Bind` (\b -> fmap a2c (b2ga b))

-- |  The function `<<||>` is a special version of `<||>`, which only starts a new instance of its right operand when the left operand cannot proceed.
--   This is used in the function 'pmMany', where we want to merge as many instances of its argument, but no more than that.

(<<||>):: Functor f => Gram f (b->a) -> Gram f b -> Gram f a
gb2a@(Gram lb2a eb2a) <<||> ~gb@(Gram _ eb)
   = Gram ( map (`fwdby` gb) lb2a)   (eb2a <*> eb)
     where (fc2b2a `Seq`   gc)      `fwdby` gb = (uncurry <$> fc2b2a) `Seq` ((,)  <$> gc <||> gb)
           (fc     `Bind`  c2gb2a)  `fwdby` gb =  fc `Bind` (\ c ->  c2gb2a c <||> gb)  


-- | The function `<||>` is the merging equivalent of `<*>`. Instead of running its two arguments consecutively, 
--   the input is split into parts which serve as input for the left operand and parts which are served to the right operand. 

gb2a <||> gb = gb2a <<||> gb <|> flip ($) <$> gb <<||> gb2a

-- | The left hand side operand is gradually transformed so we get access to its first component
instance Functor f => Applicative (Gram f) where
  pure a = Gram [] (Just a)
  Gram lb2a mb2a  <*> ~gb@(Gram lb mb) 
    =   Gram  (map (`fwdby` gb) lb2a ++ [b2a <$> fb | Just b2a <- [mb2a], fb <- lb]) (mb2a <*> mb)
        where (fc2b2a `Seq`  gc) `fwdby` gb = (uncurry <$> fc2b2a)  `Seq`  ((,) <$> gc <*> gb)
              (fc `Bind` c2gb2a) `fwdby` gb = fc  `Bind` (\b -> c2gb2a b               <*> gb)


instance Functor f => Alternative (Gram f) where
  empty                     = Gram [] Nothing
  Gram ps pe <|> Gram qs qe = Gram (ps++qs) (pe <|> qe)


-- * `Gram` is a `Monad`
instance  Functor f =>  Monad (Gram f) where
  return a = Gram [] (Just a)
  Gram lb mb >>= b2g_a = 
     let -- bindto :: Functor f => Alt f b -> (b -> Gram f a) -> Alt f a
         (f_c2b `Seq`  g_c)   `bindto` b2g_a = f_c2b `Bind` \ c2b  -> c2b <$> g_c   >>= b2g_a
         (f_c   `Bind` c2g_b) `bindto` b2g_a = f_c   `Bind` \ c    -> c2g_b c       >>= b2g_a
         la = map (`bindto` b2g_a) lb
     in case mb of
        Nothing -> Gram la Nothing
        Just b  -> let Gram lra ma =  b2g_a b
                   in  Gram (la ++ lra) ma
 


-- | 'mkParser' converts a `Gram`mar back into a parser, which can subsequenly be run.
mkP :: (Monad f, Applicative f, Alternative f) => Gram f a -> f a
mkP (Gram l_a m_a) = foldr  (<|>) (maybe empty pure m_a) 
                                  (map mkP_Alt l_a)
   where  mkP_Alt (f_b2a  `Seq`  g_b  )   = f_b2a  <*>    mkP g_b
          mkP_Alt (f_b    `Bind` b2g_a)   = f_b    >>=   (mkP . b2g_a)


-- | `sepBy` is like `mkP`, with the additional feature that we require separators between the components. Probably only useful in the permuting case.
sepBy :: (Monad f, Applicative f, Alternative f) =>  Gram f a -> f b -> f a
sepBy  g sep = mkP (insertSep sep g)

insertSep :: (Applicative f) => f b -> Gram f a -> Gram f a
insertSep sep (Gram na ea :: Gram f a) = Gram (map insertSepInAlt na) ea
   where insertSepInAlt (fb2a `Seq` gb   ) = fb2a `Seq` prefixSepInGram gb
         insertSepInAlt (fc   `Bind` c2ga) = fc `Bind` (insertSep sep . c2ga)
         prefixSepInGram (Gram na ne) = Gram (map prefixSepInAlt na) ne
         prefixSepInAlt ::  Alt f b -> Alt f b
         prefixSepInAlt (fb2a `Seq` gb)   = (sep *> fb2a) `Seq` prefixSepInGram  gb

-- | Run a sufficient number of  @p@'s in a merged fashion, but no more than necessary!!
gmList :: Functor f => Gram f a -> Gram f [a]
gmList p = let pm = ( (:) <$> p <<||> pm ) <|> pure [] in pm



