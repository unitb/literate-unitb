#include <HsFFI.h>
#ifdef __GLASGOW_HASKELL__
#include "pipeline_stub.h"
extern void __stginit_Pipeline(void);
#endif
#include <stdio.h>

extern int main()
{
    int argc = 0;
    char *arg = "allo";
    char **argv = NULL;
    hs_init(&argc, &argv);
    hs_add_root(__stginit_Pipeline);
}
