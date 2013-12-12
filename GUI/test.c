#include <HsFFI.h>
#ifdef __GLASGOW_HASKELL__
#include "safe_stub.h"
extern void __stginit_Safe(void);
#endif
#include <stdio.h>

extern void init_lib()
{
    int argc = 0;
    char *arg = "allo";
    char **argv = NULL;
    hs_init(&argc, &argv);
    hs_add_root(__stginit_Safe);
}

int main(int argc, char *argv[])
{
    int i;
    HsStablePtr x;
    hs_init(&argc, &argv);
#ifdef __GLASGOW_HASKELL__
    hs_add_root(__stginit_Safe);
#endif

    i = fibonacci_hs(40);
    printf("Fibonacci: %d\n", i);
    x = new_map();
    printf("f[ %d ] = %d\n", 1, image(x, 1));
    printf("f[ %d ] = %d\n", 2, image(x, 2));
    printf("f[ %d ] = %d\n", 3, image(x, 3));
    printf("f[ %d ] = %d\n", 4, image(x, 4));
    printf("f[ %d ] = %d\n", 5, image(x, 5));
    printf("f[ %d ] = %d\n", 6, image(x, 6));
    printf("-----\n");
    set(x, 5, 33);
    printf("f[ %d ] = %d\n", 1, image(x, 1));
    printf("f[ %d ] = %d\n", 2, image(x, 2));
    printf("f[ %d ] = %d\n", 3, image(x, 3));
    printf("f[ %d ] = %d\n", 4, image(x, 4));
    printf("f[ %d ] = %d\n", 5, image(x, 5));
    printf("f[ %d ] = %d\n", 6, image(x, 6));

    hs_exit();
    return 0;
}
