Unit-B Web
==========

This is the web interface for Literate Unit-B.

## Setup

First follow [the instructions][stack] to install Stack.

Now, make sure you have a working LaTeX setup and follow the instructions below:

* Install Alex: `stack install alex`
* Install the yesod command line tool: `stack build yesod-bin cabal-install --install-ghc`
* Install dvipng (if it's not included in your LaTeX installation):

```
sudo tlmgr update --self
sudo tlmgr install dvipng
```

If you don't have `sudo` access, see [this][tlmgr-nosudo] Stack Exchange answer.  
See the [INSTALL instructions][dvipng-install] over on CTAN for building dvipng yourself.

* The `tex2png-hs` library used for LaTeX rendering does not check for existence
of the sty files, therefore make sure that they are properly installed before
running the application. See `script/install-stylesheets-macosx.hs` of the parent
project.
* Build the libraries: `stack build`
* Launch the development server: `stack exec -- yesod devel`
* Open [http://localhost:3000/][addr] in your browser


[stack]: http://docs.haskellstack.org/en/stable/install_and_upgrade/
[tlmgr-nosudo]: http://tex.stackexchange.com/a/288639
[dvipng-install]: http://mirrors.ctan.org/dviware/dvipng/INSTALL
[addr]: http://localhost:3000/
[yesod-quickstart]: http://www.yesodweb.com/page/quickstart
