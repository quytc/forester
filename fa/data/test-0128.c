#include <stdlib.h>

int main() {

        struct T {
                struct T* next;
                struct T* prev;
        };

        struct T* x = NULL;
        struct T* y = NULL;
        struct T* z = NULL;
        struct T* k = NULL;
//      while (__nondet()) {
                y = malloc(sizeof(*y));
                y->next = x;
                x = y;

                y = malloc(sizeof(*y));
                y->next = x;
                x = y;
//      }

                z = malloc(sizeof(*x));
                x->prev = z;
                z = y;
/*        while (y != NULL) {
                x = y;
                y = y->next;
                z = y;
                free(x);
        }
*/
        return 0;

}

