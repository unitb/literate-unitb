export LIB_NAME=literate-unitb-config
git subtree split -P Z3/Version.hs -b simon/separate-$LIB_NAME
cd ..
mkdir $LIB_NAME
cd $LIB_NAME
git init
git pull ../literate-unitb-logic simon/separate-$LIB_NAME
cd ../$LIB_NAME
stack init --omit-packages
# export LIB_NAME=literate-unitb-scripts
# git subtree split -P script -b simon/separate-$LIB_NAME
# cd ..
# mkdir $LIB_NAME
# cd $LIB_NAME
# git init
# git pull ../literate-unitb simon/separate-$LIB_NAME
# cd ../$LIB_NAME
# stack init --omit-packages
