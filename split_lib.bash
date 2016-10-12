export LIB_NAME=literate-unitb-logic
git subtree split -P logic -b simon/separate-$LIB_NAME
cd ..
mkdir $LIB_NAME
cd $LIB_NAME
git init
git pull ../literate-unitb simon/separate-$LIB_NAME
cd ../$LIB_NAME
stack init --omit-packages
