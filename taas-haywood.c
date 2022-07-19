/* ============================================================================================================== */
/* == BEGIN FILE ================================================================================================ */
/* ============================================================================================================== */
/*
 ============================================================================
 Name        : taas-haywood.c
 Author      : Matthias Thimm
 Version     : 1.10
 Copyright   : GPL3
 Description : The taas-haywood solver for abstract argumentation.
               Additional (optional) parameters
               "-rseed X" explicitly set the random seed to X (default: time(NULL))
               "-maxit X" the maximal number of iterations X, afterwards "NO" is returned
                (which may not be the correct answer);
                if both "-maxit" and if "-maxitdyn" are provided, the minimum is taken
                (default: number of arguments * 1000)
               "-maxitdyn X" the maximal number of iterations X as a factor of the number
                of arguments, afterwards "NO" is returned (which may not be the correct answer);
                if both "-maxit" and if "-maxitdyn" are provided, the minimum is taken
                (default: number of arguments * 1000)
               "-restart X" the number of iterations X (as an absolute number) after which
                the search is restarted or -1 if restarts are disabled;
                if both "-restart" and "-restartdyn" are provided, the minimum is taken (default: -1)
               "-restartdyn X" the number of iterations X as a factor of the number of
                arguments after which the search is restarted or -1 if restarts are disabled;
                if both "-restart" and "-restartdyn" are provided, the minimum is taken (default: -1)
               "-greedyprob X" probability that a greedy choice is taken instead of a random one; a
                greedy choice is flipping the status of an argument such that the number of arguments in
                the neighbourhood (including the argument) incorrectly labeled before MINUS the number
                of arguments in the neighbourhood (including the argument) incorrectly labeled after
                flipping is minimal (default: 0)
               "-greedyincall X" whether to include (value '1') all arguments in greedy choice, not just the
                ones that are also incorrectly labeled , has an undefined effect if "-greedyprob" is 0
                (default: '0')
                NOTE: this feature is buggy and may result in wrong answers
               "-initout X" whether to not randomly initialise the labeling but use the all-out labeling
                (default: 0)
               "-enforceout X" if value is 1 then, whenever an argument is flipped to "in" all arguments in
                its neighbourhood are flipped to "out" (default: 0)
               "-escapeoddcycles X" if value is 1 then, whenever an argument in an odd cycle is selected to
               be flipped, it is first checked whether some argument attacking that cycle is already labeled
               "in"; if not, some argument attacking that cycle is selected instead of the original argument
               (Explanation: every odd cycle needs to be attacked in order for a stable extension
               to exist; we do not compute, however, all odd cycles but only at maximum one odd
               cycle per argument) (default: '0')
               "-randsel X" with probability X, select some random argument to be flipped (not necessarily
               a mislabeled argument); if greedyprob+randsel = 1, so ordinary random move is taken; if
               greedyprob+randsel> 1 then randsel=1-greedyprob (default: '0')
               "-locminres X" the higher X the more likely it becomes to make a full restart (i.e. randomise
                the labeling) when the number of mislabeled arguments does not decrease further. More precisely,
                at each iteration N we do a restart with probability  P(N)=1-\frac{1}{\log_b (N-N_min+X)} where
                N_min is the iteration number with the first global minimum so far. Option is disabled if X=0,
                should be set to a value in (1,2]   (default: '0')
============================================================================
*/
#define COMPUTATION_FINISHED 0
#define COMPUTATION_ABORTED__ANSWER_YES 1
#define COMPUTATION_ABORTED__ANSWER_NO  2
#define COMPUTATION_ABORTED__ANSWER_EMPTYSET  3
#define COMPUTATION_ABORTED__ANSWER_EMPTYEMPTYSET  4
#define COMPUTATION_FINISHED__EMPTY_GROUNDED  5
#define COMPUTATION_FINISHED__NONEMPTY_GROUNDED  6
#define COMPUTATION_FINISHED__ANSWER_NO  7

#define TRUE 1
#define FALSE 0
/* ============================================================================================================== */
/* ============================================================================================================== */
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <math.h>
#include <time.h>
#include <sys/types.h>

#include "util/bitset.c"
#include "util/linkedlist.c"
#include "util/miscutil.c"
#include "util/hashtable.c"
#include "util/binaryheap.c"
#include "util/raset.c"

#include "taas/taas_aaf.c"
#include "taas/taas_inout.c"
#include "taas/taas_labeling.c"
#include "taas/taas_basics.c"

#include "util/graph.c"
/* ============================================================================================================== */
/* ============================================================================================================== */

// Initialise random number generator
void init_srand(struct TaskSpecification *task){
  char* rseed = taas__task_get_value(task,"-rseed");
  if(rseed != NULL)
    srand(atoi(rseed));
  else{
    int t = time(NULL);
    //printf("%i\n", t);
    srand(time(NULL));
  }
}

//check restart setting
int init_restart(struct TaskSpecification *task, struct AAF* aaf){
  char* restart_param = taas__task_get_value(task,"-restart");
  char* restartdyn_param = taas__task_get_value(task,"-restartdyn");
  int restart;
  if(restart_param != NULL && restartdyn_param != NULL){
    restart = (atoi(restartdyn_param) * aaf->number_of_arguments) > atoi(restart_param) ? atoi(restartdyn_param) * aaf->number_of_arguments : atoi(restart_param);
  }else if(restartdyn_param != NULL)
    restart = atoi(restartdyn_param) * aaf->number_of_arguments;
  else if(restart_param != NULL)
    restart = atoi(restart_param);
  else restart = -1;
  return restart;
}

//check max iteratios setting
long init_max_iterations(struct TaskSpecification *task, struct AAF* aaf){
  char* maxitdyn = taas__task_get_value(task,"-maxitdyn");
  char* maxit = taas__task_get_value(task,"-maxit");
  long max_iterations;
  if(maxitdyn != NULL && maxit != NULL){
    max_iterations = (atoi(maxitdyn) * aaf->number_of_arguments) > atoi(maxit) ? atoi(maxitdyn) * aaf->number_of_arguments : atoi(maxit);
  }else if(maxitdyn != NULL)
    max_iterations = atoi(maxitdyn) * aaf->number_of_arguments;
  else if(maxit != NULL)
    max_iterations = atoi(maxit);
  else max_iterations = 1000 * aaf->number_of_arguments;
  return max_iterations;
}

//check greedy prob setting
float init_greedy_prob(struct TaskSpecification *task){
  char* greedyprob = taas__task_get_value(task,"-greedyprob");
  if(greedyprob != NULL)
    return atof(greedyprob);
  return 0;
}

//check greedy include all setting
int init_greedy_include_all(struct TaskSpecification *task){
  char* greedyincall = taas__task_get_value(task,"-greedyincall");
  if(greedyincall != NULL)
    return atoi(greedyincall);
  return FALSE;
}

//check initout setting
int init_init_out(struct TaskSpecification *task){
  char* init_out = taas__task_get_value(task,"-initout");
  if(init_out != NULL)
    return atoi(init_out);
  return FALSE;
}

//check enforceout setting
int init_enforce_out(struct TaskSpecification *task){
  char* enforce_out = taas__task_get_value(task,"-enforceout");
  if(enforce_out != NULL)
    return atoi(enforce_out);
  return FALSE;
}

//check escapeoddcycles setting
int init_escapeoddcycles(struct TaskSpecification *task){
  char* escapeoddcycles = taas__task_get_value(task,"-escapeoddcycles");
  if(escapeoddcycles != NULL)
    return atoi(escapeoddcycles);
  return FALSE;
}
//check randsel setting
float init_randsel(struct TaskSpecification *task){
  char* randsel = taas__task_get_value(task,"-randsel");
  if(randsel != NULL)
    return atof(randsel);
  return 0;
}

//check locminres setting
float init_locminres(struct TaskSpecification *task){
  char* locminres = taas__task_get_value(task,"-locminres");
  if(locminres != NULL)
    return atof(locminres);
  return 0;
}

// computes the flipping count of the given argument, i.e. the number of correctly labeled
// arguments in the neighbourhood of the argument MINUS the number of correctly labeled
// arguments in the neighbourhood of the argument if the argument would be flipped.
int get_flipping_count(struct AAF* aaf,struct Labeling* lab, int arg){
  int flipping_count = 0;
  int new_label = bitset__get(lab->in,arg)? LAB_OUT : LAB_IN;
  flipping_count += taas__labeled_correctly(aaf,lab,arg) ? 1 : 0;
  flipping_count += taas__labeled_correctly_under_assumption(aaf,lab,arg,arg,new_label) ? -1 : 0;
  for(struct LinkedListNode* node = aaf->children[arg].root; node != NULL; node = node->next){
    flipping_count += taas__labeled_correctly(aaf,lab,*(int*)node->data) ? 1 : 0;
    flipping_count += taas__labeled_correctly_under_assumption(aaf,lab,*(int*)node->data,arg,new_label) ? -1 : 0;
  }
  for(struct LinkedListNode* node = aaf->parents[arg].root; node != NULL; node = node->next){
    flipping_count += taas__labeled_correctly(aaf,lab,*(int*)node->data) ? 1 : 0;
    flipping_count += taas__labeled_correctly_under_assumption(aaf,lab,*(int*)node->data,arg,new_label) ? -1 : 0;
  }
  return flipping_count;
}

/**
 * Solve SE-ST
 */
void solve(struct TaskSpecification *task, struct AAF* aaf, struct Labeling* grounded){
  // in order to have pointers to the arguments
  int* all_arguments = malloc(aaf->number_of_arguments * sizeof(int));
  for(int i = 0; i < aaf->number_of_arguments; i++)
    all_arguments[i] = i;
  // do some intialising
  init_srand(task);
  //read some parameters
  int restart = init_restart(task,aaf);
  long max_iterations = init_max_iterations(task,aaf);
  float greedyprob = init_greedy_prob(task);
  int greedyincall = init_greedy_include_all(task);
  int init_out = init_init_out(task);
  int enforce_out = init_enforce_out(task);
  int escapeoddcycles = init_escapeoddcycles(task);
  float randsel= init_randsel(task);
  float locminres = init_locminres(task);
  float log_b;
  if(locminres > 0)
    log_b = 1/log(locminres);
  // check for odd cycle usage
  struct OddCycleCollection* occ = NULL;
  if(escapeoddcycles){
    occ = occ__init(aaf);
    // if we found an unattacked odd cycle we can stop right away.
    if(occ == NULL){
      printf("NO\n");
      return;
    }
  }
  // Initialise labeling
  struct Labeling* lab = malloc(sizeof(struct Labeling));
  taas__lab_init(lab,TRUE);
  bitset__init(lab->in, aaf->number_of_arguments);
  // The following data structure keeps track of the arguments that are not labeled correctly
  struct RaSet* mislabeled = raset__init_empty(aaf->number_of_arguments);
  // The following data structure collects arguments that have to be checked for their
  // correct label after some change
  struct RaSet* toBeChecked = raset__init_empty(aaf->number_of_arguments);
  // the following  heap is used as a priority queue if greedy choices are enabled,
  // i.e. it records for arguments their flipping number;
  // for each argument currently correctly labeled +1 is added; for each
  // argument labeled correctly after flipping -1 is added; thus, the smaller
  // the number, the better the flip
  struct BinaryHeap* mislabeled_pqueue = NULL;
  // the following ints remember the global minimum of the number of mislabeled arguments (so far);
  // only used if locminres > 0
  int min_mislabeled;
  int min_mislabeled_iteration;
  // the following parameter keeps track of the number of iterations;
  // the search is aborted once the maximal number of iterations is reached;
  // then "NO" is returned (meaning no stable labeling "likely" exists)
  int number_iterations = 0;
  //------------------
  // MAIN LOOP - BEGIN
  //------------------
  do{
    // check if we need to restart because we think we are in a local minimum
    int force_restart = FALSE;
    if(locminres > 0){
      // update current global minimum
      if(mislabeled->number_of_elements < min_mislabeled){
        min_mislabeled = mislabeled->number_of_elements;
        min_mislabeled_iteration = number_iterations;
      }else{
        float prob = 1-log_b/log(number_iterations-min_mislabeled_iteration+locminres);
        if((float)rand()/(float)RAND_MAX < prob)
          force_restart = TRUE;
      }
    }
    // whenever the restart parameter says so (or force_restart), randomise the labeling
    if((number_iterations == 0) || (restart != -1 && (number_iterations % restart) == 0) || force_restart){
      if(init_out){
        // use the all-out labeling
        bitset__unsetAll(lab->in);
      }else taas__lab_randomize(lab);
      // copy arguments in/out from grounded labeling, those are fixed
      for(int i = 0; i < aaf->number_of_arguments; i++){
        if(bitset__get(grounded->in,i))
          bitset__set(lab->in,i);
        else if(bitset__get(grounded->out,i))
          bitset__unset(lab->in,i);
      }
      // reset mislabeled data structures
      // NOTE: arguments in/out from the grounded labeling are always labeled correctly
      raset__reset(mislabeled);
      for(int i = 0; i < aaf->number_of_arguments; i++)
        if(!bitset__get(grounded->in,i)&&!bitset__get(grounded->out,i))
            if(!taas__labeled_correctly(aaf,lab,i))
              raset__add(mislabeled,i);
      // if we already have a stable labeling, break
      if(mislabeled->number_of_elements == 0)
        break;
      // store minimum mislabeled number
      if(locminres > 0){
        min_mislabeled = mislabeled->number_of_elements;
        min_mislabeled_iteration = 0;
      }
      // reset greedy choice datastructures, if needed
      if(greedyprob>0){
        // destroy the old heap
        if(mislabeled_pqueue != NULL)
          binaryheap__destroy(mislabeled_pqueue);
        //create a new one
        mislabeled_pqueue = malloc(sizeof(struct BinaryHeap));
        binaryheap__init(mislabeled_pqueue, aaf->number_of_arguments);
        // determine for each mislabeled argument (if greedyincall = false) or
        // for each argument (if greedyincall = true) its "flipping number";
        // for the latter also ignore arguments in/out the grounded labeling
        if(greedyincall)
          for(int i = 0; i < aaf->number_of_arguments; i++){
            if(!bitset__get(grounded->in,i)&&!bitset__get(grounded->out,i))
              binaryheap__insert(mislabeled_pqueue,&all_arguments[i],get_flipping_count(aaf,lab,i));
          }
        else
          for(int i = 0; i < mislabeled->number_of_elements; i++){
            int elem = raset__get(mislabeled,i);
            binaryheap__insert(mislabeled_pqueue,&all_arguments[elem],get_flipping_count(aaf,lab,elem));
          }
      }
    }
    // check iteration count
    number_iterations++;
    if(number_iterations >= max_iterations)
      break;
    //pick 1.) a mislabled argument at random or
    // 2.) do a greedy move, or
    // 3.) pick an arbitrary argument at random
    int sel_arg;
    float prob = (float)rand() / (float)RAND_MAX;
    if(prob < greedyprob && mislabeled_pqueue->length>0){
      sel_arg = *binaryheap__extract_minimum(mislabeled_pqueue);
    }else if(prob < greedyprob + randsel){
      // select some argument that is not in/out the grounded labeling
      do{
        sel_arg = rand() % aaf->number_of_arguments;
      }while(bitset__get(grounded->in,sel_arg)|| bitset__get(grounded->out,sel_arg));
    }else{
      sel_arg = raset__random_element(mislabeled);
    }
    // reset toBeChecked
    raset__reset(toBeChecked);
    // if the selected argument is a member of an odd cycle and there is no
    // argument attacking that cycle labelled in, select such an attacker instead
    // (only if odd cycles have been computed)
    if(occ != NULL && occ__contains(occ,sel_arg)){
      struct RaSet* attackers = occ__get_attackers(occ,sel_arg);
      // if there is at least one attacker already labelled in, everything is fine
      int all_out = TRUE;
      for(int i = 0; i < attackers->number_of_elements; i++)
        if(bitset__get(lab->in, raset__get(attackers, i))){
          all_out = FALSE;
          break;
        }
      // select an attacker at random (but not an argument already labeled out
      // in the grounded labeling)
      if(all_out){
        sel_arg = raset__random_element_with_skip(attackers,grounded->out);
        if(sel_arg == -1){
          // all attackers of the odd cycle are out in the grounded labeling
          // this means there cannot be a stable labeling
          break;
        }
      }
    }
    // toggle label
    if(taas__lab_get_label(lab,sel_arg) == LAB_IN){
      bitset__unset(lab->in,sel_arg);
      // add the argument itself to toBeChecked
      raset__add(toBeChecked,sel_arg);
    }else{
      // if the selected argument is self-attacking, select
      // an attacker of that argument instead
      if(bitset__get(aaf->loops,sel_arg)){
        int number_of_attackers = aaf->parents->length;
        // if there is no attacker there cannot be a stable extension
        if(number_of_attackers == 0)
             break;
        // pick new argument (but not an argument labeled out in the grounded labeling)
        void* r = llist__get_with_skip(aaf->parents,rand() % number_of_attackers,grounded->out);
        if(r == NULL){
          // all attackers of the loop are out in the grounded labeling
          // this means there cannot be a stable labeling
          break;
        }else sel_arg = *(int*) r;
      }
      // label it in
      bitset__set(lab->in,sel_arg);
      // add the argument itself to toBeChecked
      raset__add(toBeChecked,sel_arg);
      // if "enforceout" is true then all arguments in the neighbourhood are
      // labeled out
      // NOTE: by doing so we cannot accidently re-label an argument from the
      // grounded extension
      if(enforce_out){
        //while setting the neighbourhood to out,
        //add the indirect neighbourhood to toBeChecked
        for(struct LinkedListNode* node = aaf->children[sel_arg].root; node != NULL; node = node->next){
          bitset__unset(lab->in, *(int*)node->data);
          for(struct LinkedListNode* node2 = aaf->children[*(int*)node->data].root; node2 != NULL; node2 = node2->next)
            raset__add(toBeChecked,*(int*)node2->data);
          for(struct LinkedListNode* node2 = aaf->parents[*(int*)node->data].root; node2 != NULL; node2 = node2->next)
            raset__add(toBeChecked,*(int*)node2->data);
        }
        for(struct LinkedListNode* node = aaf->parents[sel_arg].root; node != NULL; node = node->next){
          bitset__unset(lab->in, *(int*)node->data);
          for(struct LinkedListNode* node2 = aaf->children[*(int*)node->data].root; node2 != NULL; node2 = node2->next)
            raset__add(toBeChecked,*(int*)node2->data);
          for(struct LinkedListNode* node2 = aaf->parents[*(int*)node->data].root; node2 != NULL; node2 = node2->next)
            raset__add(toBeChecked,*(int*)node2->data);
        }
      }
    }
    //add the direct neighbourhood to toBeChecked
    for(struct LinkedListNode* node = aaf->children[sel_arg].root; node != NULL; node = node->next)
      raset__add(toBeChecked,*(int*)node->data);
    for(struct LinkedListNode* node = aaf->parents[sel_arg].root; node != NULL; node = node->next)
      raset__add(toBeChecked,*(int*)node->data);
    // check direct/indirect neighbourhood of selected argument for changes; skip
    // arguments in/out from the grounded labeling, they are always correct
    for(int i = 0 ; i < toBeChecked->number_of_elements; i++){
      int elem = raset__get(toBeChecked,i);
      if(!bitset__get(grounded->in,elem)&&!bitset__get(grounded->out,elem)){
        int labeled_correctly = taas__labeled_correctly(aaf,lab,elem);
        if(!labeled_correctly)
          raset__add(mislabeled,elem);
        else
          raset__remove(mislabeled,elem);
        // update greedy structures
        if(greedyprob > 0 && (!labeled_correctly || greedyincall))
          binaryheap__update(mislabeled_pqueue,&all_arguments[elem],get_flipping_count(aaf,lab,elem));
        else if(greedyprob > 0 && labeled_correctly && !greedyincall && binaryheap__contains(mislabeled_pqueue,&all_arguments[elem])){
          binaryheap__remove(mislabeled_pqueue,&all_arguments[elem]);
        }
      }
    }
  }while(mislabeled->number_of_elements > 0);
  //------------------
  // MAIN LOOP - END
  //------------------
  // it seems we found a stable labeling
  if(mislabeled->number_of_elements == 0)
    printf("%s\n",taas__lab_print(lab,aaf));
  else
    printf("NO\n");
  // free some variables
  if(occ != NULL)
    occ__destroy(occ);
  taas__lab_destroy(lab);
  raset__destroy(mislabeled);
  if(mislabeled_pqueue != NULL)
    binaryheap__destroy(mislabeled_pqueue);
  return;
}

/* ============================================================================================================== */
int main(int argc, char *argv[]){
  // General solver information
	struct SolverInformation *info = taas__solverinformation(
			"taas-haywood v1.10 (2019-04-24)\nMatthias Thimm (thimm@uni-koblenz.de)",
			"[tgf]",
			"[SE-GR,EE-GR,DC-GR,DS-GR,SE-CO,DS-CO,SE-ST]"
		);
  return taas__solve(argc,argv,info,solve);
}

/* ============================================================================================================== */
/* == END FILE ================================================================================================== */
/* ============================================================================================================== */
