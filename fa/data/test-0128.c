/*
 * Linux driver snippet
 *
 * boxes:
 */

#include <stdlib.h>

//  int __nondet();

  struct node{
    struct node *next;
    struct node *next1;
    struct node *next2;
  //  int data;
  };
 int main()
 {
    struct node* x= malloc(sizeof (struct node));
    struct node* y = malloc(sizeof (struct node));
    struct node* z = malloc(sizeof (struct node));
    x->next = y;
    x->next1 = y;
    x->next2 = y;
    y->next = z;
    free(x);
    free(z);
    free(y);
    return 0;
 }
