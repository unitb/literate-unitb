Literate Unit-B (Web Prover)
============================

This is the web interface for Literate Unit-B.

## Setup

First follow [the instructions][stack] to install Stack.

Now,

* Install the yesod command line tool: `stack build yesod-bin cabal-install --install-ghc`
* Build the libraries: `stack build`
* Launch the development server: `stack exec -- yesod devel`
* Open [http://localhost:3000/][addr] in your browser

(Taken from the [Yesod quick start guide][yesod-quickstart].)


[stack]: http://docs.haskellstack.org/en/stable/install_and_upgrade/
[addr]: http://localhost:3000/
[yesod-quickstart]: http://www.yesodweb.com/page/quickstart
