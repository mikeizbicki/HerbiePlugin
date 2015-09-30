-- | This module handles parsing the options that can get passed into the HerbiePlugin
module Herbie.Options
    where

import GhcPlugins
import Prelude

data PluginOpts = PluginOpts
    {
    -- | This comment will be stored in the Herbie database for each expression that is found
    optsComments  :: String

    -- | Controls whether rewriting is enabled or not
    , optsRewrite   :: Bool

    -- | Perform the rewrite only if the improved expression reduces instability
    -- by this number of bits
    , optsTol       :: Double
    }

defPluginOpts :: PluginOpts
defPluginOpts = PluginOpts
    { optsComments = ""
    , optsRewrite = True
    , optsTol = 0.5
    }

parsePluginOpts :: [CommandLineOption] -> PluginOpts
parsePluginOpts xs = go xs defPluginOpts
    where
        go []     opts = opts
        go (x:xs) opts
            | take 9 x == "noRewrite"   = go xs $ opts { optsRewrite = False }
            | take 4 x == "tol="        = go xs $ opts { optsTol = read (drop 4 x) }
            | take 8 x == "comment="    = go xs $ opts { optsComments = drop 8 x }
            | otherwise                 = go xs opts
