/******************************************************
 * Ngaro
 *
 *|F|
 *|F| FILE: vm.c
 *|F|
 *
 * Written by Charles Childers, released into the public
 * domain
 ******************************************************/

#include "functions.h"
#include "vm.h"

#include "SDL.h"

/* Variables specific to the VM */
VM_STATE vm;



/******************************************************
 *|F| void init_vm()
 *
 * This zeros out everything in the VM_STATE struct
 * to give us a known starting point.
 ******************************************************/
void init_vm()
{
   int a;
   vm.ip = vm.sp = vm.rsp = 0;
   for (a = 0; a < STACK_DEPTH; a++)
      vm.data[a] = 0;
   for (a = 0; a < ADDRESSES; a++)
      vm.address[a] = 0;
   for (a = 0; a < IMAGE_SIZE; a++)
      vm.image[a] = 0;
   for (a = 0; a < 1024; a++)
      vm.ports[a] = 0;
}



/******************************************************
 *|F| void vm_process()
 *
 * This is a simple switch-based processor with one
 * case for each opcode. It's not the fastest approach,
 * but is easy enough to follow, add on to, and works
 * well enough for my current needs.
 ******************************************************/
void vm_process(int opcode) {
  int a, b;

  switch(opcode)
  {
    /***************************************************/
    /* NOP    Does Nothing. Used for padding           */
    /* Opcode: 0        Stack:  -       Address: -     */
    case VM_NOP:
         break;

    /***************************************************/
    /* LIT    Push the value in the following cell to  */
    /*        the stack                                */
    /* Opcode: 1 n      Stack: -n       Address: -     */
    case VM_LIT:
         vm.sp++;
         vm.ip++;
         TOS = vm.image[vm.ip];
         break;

    /***************************************************/
    /* DUP    Duplicate the value on the top of the    */
    /*        stack                                    */
    /* Opcode: 2        Stack: n-nn     Address: -     */
    case VM_DUP:
         vm.sp++;
         vm.data[vm.sp] = NOS;
         break;

    /***************************************************/
    /* DROP   Drop the value on the top of the stack   */
    /* Opcode: 3        Stack: n-       Address: -     */
    case VM_DROP:
         DROP
         break;

    /***************************************************/
    /* SWAP   Exchange the top two values on the stack */
    /* Opcode: 4        Stack: xy-yx    Address: -     */
    case VM_SWAP:
         a = TOS;
         TOS = NOS;
         NOS = a;
         break;

    /***************************************************/
    /* PUSH   Move the top value on the stack to the   */
    /*        address stack. Remove it from the data   */
    /*        stack.                                   */
    /* Opcode: 5        Stack: n-       Address: -n    */
    case VM_PUSH:
         vm.rsp++;
         TORS = TOS;
         DROP
         break;

    /***************************************************/
    /* POP    Move the top value from the address      */
    /*        stack to the data stack. Remove it from  */
    /*        the address stack.                       */
    /* Opcode: 6        Stack: -n       Address: n-    */
    case VM_POP:
         vm.sp++;
         TOS = TORS;
         vm.rsp--;
         break;

    /***************************************************/
    /* CALL   Call a subroutine whose address is given */
    /*        in the following cell. Push the address  */
    /*        following this instruction to the address*/
    /*         stack.                                  */
    /* Opcode: 7 a       Stack: -      Address: -a     */
    case VM_CALL:
         vm.ip++;
         vm.rsp++;
         TORS = vm.ip;
         vm.ip = vm.image[vm.ip] - 1;
         break;

    /***************************************************/
    /* JUMP   Unconditional jump to the address given  */
    /*        in the following cell.                   */
    /* Opcode: 8 a       Stack: -       Address: -     */
    case VM_JUMP:
         vm.ip++;
         vm.ip = vm.image[vm.ip] - 1;
         break;

    /***************************************************/
    /* ;      Return from a subroutine. Control is     */
    /*        passed to the address on the top of the  */
    /*        address stack.                           */
    /* Opcode: 9         Stack: -       Address: a-    */
    case VM_RETURN:
         vm.ip = TORS;
         vm.rsp--;
         break;

    /***************************************************/
    /* >JUMP  Jump to the address in the following     */
    /*        cell if NOS > TOS.                       */
    /* Opcode: 10 a      Stack: xy-     Address: -     */
    case VM_GT_JUMP:
         vm.ip++;
         if(NOS > TOS)
           vm.ip = vm.image[vm.ip] - 1;
         DROP DROP
         break;

    /***************************************************/
    /* <JUMP  Jump to the address in the following     */
    /*        cell if NOS < TOS.                       */
    /* Opcode: 11 a      Stack: xy-     Address: -     */
    case VM_LT_JUMP:
         vm.ip++;
         if(NOS < TOS)
           vm.ip = vm.image[vm.ip] - 1;
         DROP DROP
         break;

    /***************************************************/
    /* !JUMP  Jump to the address in the following     */
    /*        cell if NOS <> TOS.                      */
    /* Opcode: 12 a      Stack: xy-     Address: -     */
    case VM_NE_JUMP:
         vm.ip++;
         if(TOS != NOS)
           vm.ip = vm.image[vm.ip] - 1;
         DROP DROP
         break;

    /***************************************************/
    /* =JUMP  Jump to the address in the following     */
    /*        cell if NOS = TOS.                       */
    /* Opcode: 13 a      Stack: xy-     Address: -     */
    case VM_EQ_JUMP:
         vm.ip++;
         if(TOS == NOS)
           vm.ip = vm.image[vm.ip] - 1;
         DROP DROP
         break;

    /***************************************************/
    /* @      Fetch a value from a memory location     */
    /* Opcode: 14        Stack: a-n     Address: -     */
    case VM_FETCH:
         TOS = vm.image[TOS];
         break;

    /***************************************************/
    /* !      Store a value to a memory location       */
    /* Opcode: 15        Stack: na-     Address: -     */
    case VM_STORE:
         vm.image[TOS] = NOS;
         DROP DROP
         break;

    /***************************************************/
    /* +      Add TOS and NOS, leaving the result      */
    /* Opcode: 16        Stack: xy-z    Address: -     */
    case VM_ADD:
         NOS += TOS;
         DROP
         break;

    /***************************************************/
    /* -      Subtract TOS from NOS, leaving the result*/
    /* Opcode: 17        Stack: xy-z    Address: -     */
    case VM_SUB:
         NOS -= TOS;
         DROP
         break;

    /***************************************************/
    /* *      Multiply TOS by NOS, leaving the result  */
    /* Opcode: 18        Stack: xy-z    Address: -     */
    case VM_MUL:
         NOS *= TOS;
         DROP
         break;

    /***************************************************/
    /* /MOD   Divide NOS by TOS, leaving the quotient  */
    /*        and remainder.                           */
    /* Opcode: 19        Stack: xy-qr   Address: -     */
    case VM_DIVMOD:
         a = TOS;
         b = NOS;
         TOS = b / a;
         NOS = b % a;
         break;

    /***************************************************/
    /* AND    Perform a bitwise and operation on TOS   */
    /*        and NOS.                                 */
    /* Opcode: 20        Stack: xy-z    Address: -     */
    case VM_AND:
         a = TOS;
         b = NOS;
         DROP
         TOS = a & b;
         break;

    /***************************************************/
    /* OR     Perform a bitwise or operation on TOS    */
    /*        and NOS.                                 */
    /* Opcode: 21        Stack: xy-z    Address: -     */
    case VM_OR:
         a = TOS;
         b = NOS;
         DROP
         TOS = a | b;
         break;

    /***************************************************/
    /* XOR    Perform a bitwise xor operation on TOS   */
    /*        and NOS.                                 */
    /* Opcode: 22        Stack: xy-z    Address: -     */
    case VM_XOR:
         a = TOS;
         b = NOS;
         DROP
         TOS = a ^ b;
         break;

    /***************************************************/
    /* <<    Shift NOS left by TOS bits.               */
    /* Opcode: 23        Stack: xy-z    Address: -     */
    case VM_SHL:
         a = TOS;
         b = NOS;
         DROP
         TOS = b << a;
         break;

    /***************************************************/
    /* >>    Shift NOS right by TOS bits.              */
    /* Opcode: 24        Stack: xy-z    Address: -     */
    case VM_SHR:
         a = TOS;
         b = NOS;
         DROP
         TOS = b >>= a;
         break;

    /***************************************************/
    /* 0;    Return from a subroutine if TOS = 0.      */
    /*       If TOS = 0, DROP TOS.                     */
    /*       If TOS <> 0, do nothing                   */
    /* Opcode: 25         Stack: n-     Address: a-    */
    /*                    Stack: n-n    Address: -     */
    case VM_ZERO_EXIT:
         if (TOS == 0)
         {
           DROP
           vm.ip = TORS;
           vm.rsp--;
         }
         break;

    /***************************************************/
    /* 1+    Increase TOS by 1                         */
    /* Opcode: 26        Stack: x-y     Address: -     */
    case VM_INC:
         TOS += 1;
         break;

    /***************************************************/
    /* 1-    Decrease TOS by 1                         */
    /* Opcode: 27        Stack: x-y     Address: -     */
    case VM_DEC:
         TOS -= 1;
         break;

    /***************************************************/
    /* IN    Read a value from an I/O port             */
    /* Opcode: 28        Stack: p-n     Address: -     */
    case VM_IN:
         a = TOS;
         TOS = vm.ports[a];
         vm.ports[a] = 0;
         break;

    /***************************************************/
    /* OUT   Send a value to an I/O port               */
    /* Opcode: 29        Stack: np-     Address: -     */
    case VM_OUT:
         vm.ports[0] = 0;
         vm.ports[TOS] = NOS;
         DROP DROP
         break;

    /***************************************************/
    /* WAIT  Wait for an I/O event to occur.           */
    /* Opcode: 30        Stack: -       Address: -     */
    case VM_WAIT:
         handle_devices(0);
         break;

    /***************************************************/
    /* ----  Any other opcodes are invalid, suspend    */
    /*       execution if encountered.                 */
    default:
         vm.ip = IMAGE_SIZE;
         break;
  }
}
