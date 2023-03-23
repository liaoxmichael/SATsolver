// Michael Liao
// CSC 372 Artificial Intelligence
// A3
/* Description:
    This file will read in the SAT problems from external DIMACS-format files
    and process them with a variety of SAT solving techniques: DPLL, WalkSAT,
    and a genetic algorithm.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdbool.h>

#define MAX_CLAUSE_LENGTH 5
#define SEED 21
#define UNDET 0
#define UNSAT -1
#define SAT 1
#define S_CNF_FILE "A3_tests/10.40.160707067.cnf" // for debugging purposes
#define U_CNF_FILE "A3_tests/10.44.1247388329.cnf" // for debugging purposes
#define GET_INDEX(x) (abs(x)-1)

typedef struct { // going to store our SAT problem
    int num_clauses; // size of above array
    int num_variables; // no need to create an array to store symbols because they range from 1:num_variables
    int **clauses;
} SAT_problem;

void intAdeepCopy(int dest[], int src[], int size) { // writing own b/c memcpy slow
    for (int i=0; i<size; i++) {
        dest[i] = src[i];
    }
}
void printArr(int arr[], int size) { // debugger stopped working so now i do everything manually. awesome
    for (int i=0; i<size; i++) {
        printf("%d ", arr[i]);
    }
    printf("\n");
}
float randFloat() {
    return rand() / (RAND_MAX + 1.0);
}

SAT_problem readInFile(char *filename) {
    FILE *input;
    input = fopen(filename,"r");
    if (input == NULL) {
        printf("%s not found.\n", filename);
        exit(1);
    }

    SAT_problem prob;
    char *line = NULL;
    char *token = NULL;
    size_t line_buffer_size = 0;

    do { // skipping all initial comments; after loop finishes, we should be on line containing p cnf X Y
        getline(&line, &line_buffer_size, input);
        token = strtok(line, " ");
    } while (strcmp(token, "p") != 0);

    token = strtok(NULL, " "); // skipping "cnf"
    token = strtok(NULL, " "); // this token contains the number of symbols
    prob.num_variables = atoi(token);

    token = strtok(NULL, " "); // this token contains the number of clauses
    prob.num_clauses = atoi(token);

    prob.clauses = malloc(sizeof(int *)*prob.num_clauses);
    if (prob.clauses == NULL) {
        printf("error in malloc for clauses!\n");
        exit(1);
    }
    for (int i=0; i<prob.num_clauses; i++) {
        prob.clauses[i] = malloc(sizeof(int)*MAX_CLAUSE_LENGTH); // arbitrarily assuming max length of a clause
        if (prob.clauses[i] == NULL) {
            printf("error in malloc for individual disjunct clauses!\n");
            exit(1);
        }
    }
    int j = 0;
    for (int i=0; i<prob.num_clauses; i++) { // getting all clauses
        getline(&line, &line_buffer_size, input);
        token = strtok(line, " ");
        if (strcmp(token, "c")==0) { // skipping comments
            getline(&line, &line_buffer_size, input);
            token = strtok(NULL, " ");
        }
        j=0;
        while(strcmp(token, "0\n")!=0) {
            prob.clauses[i][j] = atoi(token);
            token = strtok(NULL, " ");
            j++;
        }
        while (j<MAX_CLAUSE_LENGTH) {
            prob.clauses[i][j] = 0; // filling remaining parts of clause
            j++;
        }
    }
    fclose(input);
    return prob;
}

int findPureSymbol(SAT_problem prob, int *marked_clauses, int *symbols, int *model) { // going to iterate through UNSAT clauses (assuming pure variables) and mark any differences
    int result;
    int *check = malloc(sizeof(int) * prob.num_variables); // creating an array to hold the first instance found
    for (int i=0; i<prob.num_variables; i++) { // initializing all to 0
        check[i] = 0;
    }
    for (int i=0; i<prob.num_clauses; i++) { // scanning thru every clause
        for (int j=0; j<MAX_CLAUSE_LENGTH && prob.clauses[i][j] != 0 && marked_clauses[i] != SAT; j++) { // skipping clauses that are already SAT
            if (check[GET_INDEX(prob.clauses[i][j])] == 0) { // if current symbol has not appeared yet
                check[GET_INDEX(prob.clauses[i][j])] = prob.clauses[i][j];
            } else if (check[GET_INDEX(prob.clauses[i][j])] != prob.clauses[i][j]) { // if current symbol has appeared but are not same
                check[GET_INDEX(prob.clauses[i][j])] = prob.num_variables + 1; // would not exist in this problem's context
            }
        }
    }
    for (int i=0; i<prob.num_variables; i++) {
        if ((check[i] != 0) && (check[i] != prob.num_variables+1) && (symbols[GET_INDEX(check[i])] != 0)) {
            result = check[i];
            free(check);
            return result; 
        }
    }
    free(check);
    return 0; // return 0 if no pure symbol found
}
int findUnitClause(SAT_problem prob, int *marked_clauses, int *symbols, int *model) { // going to iterate through UNSAT clauses and see which ones are reducible based on current assignments
    for (int i=0; i<prob.num_clauses; i++) { // walk through every clause
        int num_unassigned = 0; // keeping track of unassigned variables; if more than 1, not unit clause
        int unassigned_variable = 0;
        for (int j=0; 
            j<MAX_CLAUSE_LENGTH && prob.clauses[i][j] != 0 && num_unassigned < 2 && marked_clauses[i] != SAT;
            j++) { // walk through every variable in clause
            if (model[GET_INDEX(prob.clauses[i][j])] == 0) { // if current variable is unassigned in model
                num_unassigned++;
                unassigned_variable = prob.clauses[i][j]; // storing the literal we need to SAT this clause
            }
        }
        if ((num_unassigned == 1) && (symbols[GET_INDEX(unassigned_variable)] == 0)) { // implying every other statement is false (because we are ignoring SAT clauses) and one is assigned
            return unassigned_variable;
        }
    }
    return 0; // if no unit clause found, return 0
}
bool DPLL(SAT_problem prob, int *marked_clauses, int *symbols, int *model, int *count) { // recursive call
    (*count)++;
    bool result;
    int *this_symbols = malloc(sizeof(int) * prob.num_variables);
    int *this_marked_clauses = malloc(sizeof(int) * prob.num_clauses);
    int *this_model = malloc(sizeof(int) * prob.num_variables);
    intAdeepCopy(this_symbols, symbols, prob.num_variables);
    intAdeepCopy(this_marked_clauses, marked_clauses, prob.num_clauses);
    intAdeepCopy(this_model, model, prob.num_variables);
    
    /* printf("Symbols: "); printArr(this_symbols, prob.num_variables); // debug
    printf("Marked Clauses: "); printArr(this_marked_clauses, prob.num_clauses); // debug
    printf("Model: "); printArr(this_model, prob.num_variables); // debug */
   
    for (int i=0; i<prob.num_clauses; i++) { // checking if all clauses are SAT; if one UNSAT, return False
        if (this_marked_clauses[i] == UNDET) { // need to check if this clause is SAT or not
            int identifier = 0;
            int num_false = 0;
            int num_variables = 0;
            for (int j=0; j<MAX_CLAUSE_LENGTH && prob.clauses[i][j] != 0 && identifier <= 0; j++) { // if one of the items here is true, whole statement is true
                identifier = prob.clauses[i][j] * this_model[GET_INDEX(prob.clauses[i][j])]; // if unassigned, identifier will be 0; if opposites, identifier will be neg
                if (identifier < 0) {
                    num_false++;
                }
                num_variables++;
            }
            if (identifier > 0) {
                this_marked_clauses[i] = SAT;
            } else if (num_false == num_variables) {
                this_marked_clauses[i] = UNSAT;
                // printf("Clause %d UNSAT\n", i); //debug
                // printArr(prob.clauses[i], MAX_CLAUSE_LENGTH); //debug
                free(this_symbols);
                free(this_marked_clauses);
                free(this_model);
                return false;
            }
        } else if (this_marked_clauses[i] == UNSAT) {
            free(this_symbols);
            free(this_marked_clauses);
            free(this_model);
            return false;
        }
    }
    bool all_SAT = true;
    for (int i=0; i<prob.num_clauses && all_SAT != false; i++) {
        if (this_marked_clauses[i] != SAT) {
            // printf("Clause %d not SAT, actually %d\n", i, this_marked_clauses[i]); //debug
            // printArr(prob.clauses[i], MAX_CLAUSE_LENGTH); //debug
            all_SAT = false;
        }
    }
    if (all_SAT) {
        printArr(this_model, prob.num_variables);
        free(this_symbols);
        free(this_marked_clauses);
        free(this_model);
        return true;
    }
    int value = findPureSymbol(prob, this_marked_clauses, this_symbols, this_model);
    if (value != 0) { // 0 indicates no symbol found, else a symbol will be returned in its pos/neg form
        this_symbols[GET_INDEX(value)] = 0; // removing symbol from remaining options
        this_model[GET_INDEX(value)] = value; // adding our assignment to the model
        // printf("Pure symbol found: %d\n", value); //debug
        result = DPLL(prob, this_marked_clauses, this_symbols, this_model, count); 
        free(this_symbols);
        free(this_marked_clauses);
        free(this_model);
        return result;
    }
    
    value = findUnitClause(prob, this_marked_clauses, this_symbols, this_model);
    if (value != 0) {
        this_symbols[GET_INDEX(value)] = 0; // removing symbol from remaining options
        this_model[GET_INDEX(value)] = value; // adding our assignment to the model
        // printf("Unit clause found: %d\n", value); //debug
        result = DPLL(prob, this_marked_clauses, this_symbols, this_model, count); 
        free(this_symbols);
        free(this_marked_clauses);
        free(this_model);
        return result;
    }

    // otherwise, grab first symbol in symbols
    int j = 0;
    while (j<prob.num_variables && symbols[j] == 0) { // incrementing until first nonzero symbol found
        j++;
    }
    int first = symbols[j];
    // printf("Arbitrarily assigning: %d\n", first); //debug
    this_symbols[j] = 0;
    this_model[first-1] = first;
    int *model1 = malloc(sizeof(int) * prob.num_variables);
    intAdeepCopy(model1, this_model, prob.num_variables); // creating two arrays to pass forward
    this_model[first-1] = -first;
    int *model2 = malloc(sizeof(int) * prob.num_variables);
    intAdeepCopy(model2, this_model, prob.num_variables);
    result = DPLL(prob, this_marked_clauses, this_symbols, model1, count) || DPLL(prob, this_marked_clauses, this_symbols, model2, count);
    free(this_symbols);
    free(this_marked_clauses);
    free(this_model);
    free(model1);
    free(model2);
    return result;
}

bool DPLLSAT(SAT_problem prob) { // returns True if solution, returns False if not
    int count = 1;
    int *cptr = &count;
    int *model = malloc(sizeof(int) * prob.num_variables);
    int *symbols = malloc(sizeof(int) * prob.num_variables);
    int *marked_clauses = malloc(sizeof(int) * prob.num_clauses); // 0 for undetermined, -1 for false, 1 for true
    for (int i=0; i<prob.num_variables; i++) {
        model[i] = 0;
        symbols[i] = i+1;
    }
    for (int j=0; j<prob.num_clauses; j++) {
        marked_clauses[j] = UNDET;
    }
    bool result = DPLL(prob, marked_clauses, symbols, model, cptr);
    free(model);
    free(symbols);
    free(marked_clauses);
    printf("Nodes expanded: %d\n", count);
    return result;
}

bool checkModelSAT(SAT_problem prob, int *marked_clauses, int *model) {
    bool isSAT = true;
    for (int i=0; i<prob.num_clauses; i++) { // checking if all clauses are SAT; if one UNSAT, return False
        int identifier = 0;
        int num_false = 0;
        int num_variables = 0;
        for (int j=0; j<MAX_CLAUSE_LENGTH && prob.clauses[i][j] != 0 && identifier <= 0; j++) { // if one of the items here is true, whole statement is true
            identifier = prob.clauses[i][j] * model[GET_INDEX(prob.clauses[i][j])]; // if opposites, identifier will be neg
            if (identifier < 0) {
                num_false++;
            }
            num_variables++;
        }
        if (identifier > 0) {
            marked_clauses[i] = SAT;
        } else if (num_false == num_variables) {
            marked_clauses[i] = UNSAT;
            isSAT = false;
        }
    }
    return isSAT;
}
int countSATclauses(SAT_problem prob, int *marked_clauses, int *model, int variable) { // if variable=0, just count; else check flipping that variable
    int counter = 0;
    int *this_marked_clauses = malloc(sizeof(int) * prob.num_clauses);
    int *this_model = malloc(sizeof(int) * prob.num_variables);
    intAdeepCopy(this_marked_clauses, marked_clauses, prob.num_clauses);
    intAdeepCopy(this_model, model, prob.num_variables);
    if (variable != 0) {
        this_model[GET_INDEX(variable)] *= -1;
    }
    for (int i=0; i<prob.num_clauses; i++) { // updating clauses with the chosen variable
        int identifier      = 0;
        int num_false       = 0;
        int num_variables   = 0;
        for (int j=0; j<MAX_CLAUSE_LENGTH && prob.clauses[i][j] != 0 && identifier <= 0; j++) { // if one of the items here is true, whole statement is true
            identifier = prob.clauses[i][j] * this_model[GET_INDEX(prob.clauses[i][j])]; // if opposites, identifier will be neg
            if (identifier < 0) {
                num_false++;
            }
            num_variables++;
        }
        if (identifier > 0) {
            this_marked_clauses[i] = SAT;
        } else if (num_false == num_variables) {
            this_marked_clauses[i] = UNSAT;
        }
    }
    for (int i=0; i<prob.num_clauses; i++) {
            if (this_marked_clauses[i] == 1) {
                counter++;
            }
        }
    free(this_marked_clauses);
    free(this_model);
    return counter;
}

int WalkSAT(SAT_problem prob, float p, int max_flips) { // returns c, the number of clauses satisfied, or the 
    srand(SEED); // for generating random number for WalkSAT for checking against p, which will be .2 to randomly walk
    int max_SAT = 0;
    int *maxSATArr = malloc(sizeof(int) * prob.num_variables);
    int *model = malloc(sizeof(int) * prob.num_variables);
    for (int i=0; i<prob.num_variables; i++) { // randomly assigning all values in the model
        model[i] = (i+1) * ((rand() % 2) * 2 -1); // randomly getting 1 or -1
    }
    //printArr(model, prob.num_variables); //debug
    int *marked_clauses = malloc(sizeof(int) * prob.num_clauses); // -1 false, 1 true
    for (int i=0; i<max_flips; i++) {
        if (checkModelSAT(prob, marked_clauses, model)) {
            printArr(model, prob.num_variables);
            printf("Solution found in %d flips out of %d.\n", i+1, max_flips);
            free(maxSATArr);
            free(model);
            free(marked_clauses);
            return prob.num_clauses; // number of clauses satisfied
        } else {
            int current_count_SAT = countSATclauses(prob, marked_clauses, model, 0);
            if (max_SAT < current_count_SAT) {
                //printf("New max: %d > %d\n", current_count_SAT, max_SAT); //debug
                max_SAT = current_count_SAT;
                intAdeepCopy(maxSATArr, model, prob.num_variables);
            }
        }

        int rand_clause_index;
        do {
            rand_clause_index = rand()%prob.num_clauses;
        } while (marked_clauses[rand_clause_index] == 1);

        int *selected_clause = prob.clauses[rand_clause_index];
        //printf("Randomly chosen clause: %d - ", rand_clause_index); printArr(selected_clause, MAX_CLAUSE_LENGTH); //debug
        int num_variables_in_clause = 0;
        for (int j=0; j<MAX_CLAUSE_LENGTH && selected_clause[j] != 0; j++) {
            num_variables_in_clause++;
        }
        if (randFloat()<p) { // random walk
            int selected_variable = selected_clause[(rand() % num_variables_in_clause)]; // randomly selecting variable in that clause
            model[GET_INDEX(selected_variable)] *= -1; // flipping that variable
            //printf("Randomly chosen variable: %d; Flipped: ", selected_variable); printArr(model, prob.num_variables); //debug
        } else { // find maximal option to flip in clause
            int max_count = -1;
            int max_count_variable = 0;
            for (int j=0; j<num_variables_in_clause; j++) {
                int curr_count = countSATclauses(prob, marked_clauses, model, selected_clause[j]);
                if (curr_count > max_count) {
                    max_count = curr_count;
                    max_count_variable = selected_clause[j];
                    //printf("Max # variables: %d; Variable: %d\n", max_count, max_count_variable); //debug
                }
            }
            model[GET_INDEX(max_count_variable)] *= -1;
            //printf("Model after flipping: "); printArr(model, prob.num_variables); //debug
        }
    }
    printArr(maxSATArr, prob.num_variables);
    printf("Cutoff reached.\n");
    free(maxSATArr);
    free(model);
    free(marked_clauses);
    return max_SAT;
}

typedef struct {
    int *representation; // binary int array encoding the model
    int fitness;
} individual;
void printIndividual(individual individual, SAT_problem prob) {
    printf("Individual: "); printArr(individual.representation, prob.num_variables);
    printf("Fitness: %d\n", individual.fitness);
}

int getFitness(SAT_problem prob, individual individual) { // returns the number of satisfied clauses
    int counter = 0;
    for (int i=0; i<prob.num_clauses; i++) {
        int identifier = 0;
        for (int j=0; j<MAX_CLAUSE_LENGTH && prob.clauses[i][j] != 0 && identifier <= 0; j++) { // if one of the items here is true, whole statement is true
            identifier = prob.clauses[i][j] * (individual.representation[GET_INDEX(prob.clauses[i][j])] * 2 -1); // if opposites, identifier will be neg
        }
        if (identifier > 0) {
            counter++;
        }
    }
    return counter;
}
void weightedRandomChoice(individual **target, individual *population, int pop_size, int weights[], int sum) {
    int random_choice = rand() % sum; // randomly choose a number [0,sum) which is guaranteed to be one of the numbers inside, find the index corresponding
    //printf("Random choice: %d\n", random_choice); //debug
    int i = 0;
    while (i<pop_size && random_choice >= weights[i]) {
        i++;
    }
    //printf("Selected: %d\n", i); // debug
    *target = &population[i];
    //printArr((*target)->representation, 40); //debug
}
void select(individual **parent1, individual **parent2, individual *population, int pop_size) {
    int sum = 0;
    int *weights = malloc(sizeof(int) * pop_size);
    for (int i=0; i<pop_size; i++) {
        sum += population[i].fitness;
        weights[i] = sum; // each position indicates max of range that selects this individual; the min would be previous position number
        //printArr(population[i].representation, 40); //debug
    }
    //printArr(weights, pop_size); //debug
    weightedRandomChoice(parent1, population, pop_size, weights, sum);
    //printf("(select) Parent1: "); printArr((*parent1)->representation, 40); //debug
    //printf("We made it past parent1\n"); //debug
    weightedRandomChoice(parent2, population, pop_size, weights, sum);
    //printf("(select) Parent2: "); printArr((*parent2)->representation, 40); //debug
    free(weights);
}
void reproduce(SAT_problem prob, individual *parent1, individual *parent2, individual *child1, individual *child2, float p) { // produces a string that mixes the two parents
    int crossover = rand() % prob.num_variables;
    //printf("Crossover index: %d\n", crossover); //debug
    float mutation_chance;
    for (int i=0; i<crossover; i++) {
        mutation_chance = randFloat();
        if (mutation_chance < p) {
            child1->representation[i] = (parent1->representation[i] + 1) % 2; // flipping the bit
        } else {
            child1->representation[i] = parent1->representation[i];
        }

        mutation_chance = randFloat();
        if (mutation_chance < p) {
            child2->representation[i] = (parent2->representation[i] + 1) % 2; // flipping the bit
        } else {
            child2->representation[i] = parent2->representation[i];
        }
    }
    for (int i=crossover; i<prob.num_variables; i++) {
        mutation_chance = randFloat();
        if (mutation_chance < p) {
            child1->representation[i] = (parent2->representation[i] + 1) % 2; // flipping the bit
        } else {
            child1->representation[i] = parent2->representation[i];
        }

        mutation_chance = randFloat();
        if (mutation_chance < p) {
            child2->representation[i] = (parent1->representation[i] + 1) % 2; // flipping the bit
        } else {
            child2->representation[i] = parent1->representation[i];
        }
    }
}

int fitnessComparator(const void *individual1, const void *individual2) { // lets us use qsort to sort by most fit to least-fit
    individual casted_individual1 = *(individual*) individual1;
    individual casted_individual2 = *(individual*) individual2;
    return casted_individual1.fitness < casted_individual2.fitness
        ? 1 
        : casted_individual1.fitness > casted_individual2.fitness 
            ? -1 
            : 0;
}
void destroyIndividual(SAT_problem prob, individual **target) {
    if (*target != NULL) {
        if ((*target)->representation != NULL) {
            free((*target)->representation);
            (*target)->representation = NULL;
        }
        free(*target);
        *target = NULL;
    }
}
void formatSolution(SAT_problem prob, int *representation) {
    for (int k=0; k<prob.num_variables; k++) { // formatting the final output
        printf("%d ", (representation[k] * 2 -1) * (k+1));
    }
    printf("\n");
}
bool earlyTerminationCheck(SAT_problem prob, individual target, int pop_size, individual *population, individual **next_generation, int *maxSATArr, int curr_index) {
    bool result = false;
    if (target.fitness == prob.num_clauses) {
        //printArr(target.representation, prob.num_variables); //solution
        result = true;
        formatSolution(prob, target.representation);
        for (int k=0; k<pop_size; k++) { // freeing population
            free(population[k].representation);
            population[k].representation = NULL;
        }
        for (int k=0; k<curr_index; k++) { // freeing next_gen
            destroyIndividual(prob, &next_generation[k]);
        }
        /* free(maxSATArr);
        printf("Solution found in %d iterations out of %d.\n", i, cutoff);
        return prob.num_clauses; */
    }
    return result;
}

int geneticSAT(SAT_problem prob, int pop_size, int cutoff) { // returns c, the number of clauses satisfied
    individual *population = malloc(sizeof(individual) * pop_size); // creating our population (malloc this!)
    for (int i=0; i<pop_size; i++) {
        population[i].representation = malloc(sizeof(int)*prob.num_variables);
        for (int j=0; j<prob.num_variables; j++) {
            population[i].representation[j] = rand() % 2;
        }
        population[i].fitness = getFitness(prob, population[i]);
        //printIndividual(population[i], prob); //debug
        if (population[i].fitness == prob.num_clauses) {
            //printArr(population[i].representation, prob.num_variables);
            formatSolution(prob, population[i].representation);
            for (int j=0; j<=i; j++) {
                free(population[j].representation);
                population[j].representation = NULL;
            }
            free(population);
            printf("Solution found in initial population.\n");
            return prob.num_clauses; // early terminate, one of the randomly generated solutions is valid
        }
    }
    
    int maxSAT = 0;
    int *maxSATArr = malloc(sizeof(int) * prob.num_variables);
    individual **next_generation = malloc(sizeof(individual*) * pop_size * 2);
    for (int i=0; i<pop_size*2; i++) {
        next_generation[i] = NULL;
    }
    for (int i=0; i<cutoff; i++) {
        float p = 1 - (float) i/(float) cutoff; // slowly decreasing the mutation rate according to Hassanat, et al. (Choosing Mutation and Crossover Ratios for Genetic Algorithms — A Review with a New Dynamic Approach)
        //float p = 0.1;
        //printf("p = %f\n", p); //debug

        individual *parent1 = NULL, *parent2 = NULL;
        for (int j=0; j<pop_size; j++) {
            individual *child1 = malloc(sizeof(individual)), *child2 = malloc(sizeof(individual));
            child1->representation = malloc(sizeof(int)*prob.num_variables);
            child2->representation = malloc(sizeof(int)*prob.num_variables);
            /* memset(child1, 0, sizeof(struct individual));
            memset(child2, 0, sizeof(struct individual)); */
            select(&parent1, &parent2, population, pop_size);
            //printf("Parent1: "); printArr(parent1->representation, prob.num_variables); //debug
            //printf("Parent2: "); printArr(parent2->representation, prob.num_variables); //debug
            reproduce(prob, parent1, parent2, child1, child2, p);
            //printf("Child1: "); printArr(child1->representation, prob.num_variables); //debug
            //printf("Child2: "); printArr(child2->representation, prob.num_variables); //debug
            //printf("i=%d, j=%d out of %d\n", i, j, pop_size*2); //debug
            child1->fitness = getFitness(prob, *child1);
            if (earlyTerminationCheck(prob, *child1, pop_size, population, next_generation, maxSATArr, j)) {
                free(maxSATArr);
                free(child1->representation);
                free(child1);
                free(population);
                free(next_generation);
                printf("Solution found in %d generation(s) out of %d.\n", i+1, cutoff);
                return prob.num_clauses;
            } else if (child1->fitness > maxSAT) {
                //printf("Generation %d: New max: %d > %d, from model: ", i, child1->fitness, maxSAT); printArr(child1->representation, prob.num_variables); //debug
                maxSAT = child1->fitness;
                intAdeepCopy(maxSATArr, child1->representation, prob.num_variables);
                //printf("maxSATArr: "); printArr(maxSATArr, prob.num_variables); //debug
            } 
            child2->fitness = getFitness(prob, *child2);
            if (earlyTerminationCheck(prob, *child2, pop_size, population, next_generation, maxSATArr, j)) {
                free(maxSATArr);
                free(child1->representation);
                free(child1);
                free(population);
                free(next_generation);
                printf("Solution found in %d iterations out of %d.\n", i, cutoff);
                return prob.num_clauses;
            } else if (child2->fitness > maxSAT) {
                //printf("Generation %d: New max: %d > %d, from model: ", i, child1->fitness, maxSAT); printArr(child1->representation, prob.num_variables); //debug
                maxSAT = child2->fitness;
                intAdeepCopy(maxSATArr, child2->representation, prob.num_variables);
                //printf("maxSATArr: "); printArr(maxSATArr, prob.num_variables); //debug
            } 
            destroyIndividual(prob, &next_generation[2*j]);
            next_generation[2*j] = child1;
            destroyIndividual(prob, &next_generation[2*j+1]);
            next_generation[2*j+1] = child2;
            //printArr(next_generation[2*j]->representation, prob.num_variables);//debug
            //printArr(next_generation[2*j+1]->representation, prob.num_variables);//debug
        }
        qsort(next_generation, pop_size*2, sizeof(individual*), fitnessComparator); // sorting by fitness
        for (int j=0; j<pop_size; j++) { // culling half of individuals, removing lower fitness ones
            population[j].fitness = next_generation[j]->fitness;
            intAdeepCopy(population[j].representation, next_generation[j]->representation, prob.num_variables);
            //printf("%d: ", j); printArr(population[j].representation, prob.num_variables);//debug
        }
    }
    formatSolution(prob, maxSATArr);
    free(maxSATArr);
    for (int k=0; k<pop_size*2; k++) {
        destroyIndividual(prob, &next_generation[k]);
        /* if (next_generation[k] != NULL) {
            if (next_generation[k]->representation != NULL) {
                free(next_generation[k]->representation);
                next_generation[k]->representation = NULL;
            }
            free(next_generation[k]);
            next_generation[k] = NULL;
        } */
    }
    free(population);
    free(next_generation);
    printf("Cutoff reached.\n");
    return maxSAT;
}

void printclauses(SAT_problem prob) {
    for (int i=0; i<prob.num_clauses; i++) {
        for (int j=0; j<MAX_CLAUSE_LENGTH && prob.clauses[i][j] != 0; j++) {
            printf("%d ", prob.clauses[i][j]);
        }
        printf("\n");
    }
}

/*
int partition(char **population, int pop_size, int fitnesses[], int low, int high) {
    int pivot_fitness = fitnesses[low];
    int j = low; //
    for (int i=low; i<=high; i++) {
        if (fitnesses[i] < pivot_fitness) {
            j++;
            // swap all relevant items
            int temp = fitnesses[j];
            fitnesses[j] = fitnesses[i];
            fitnesses[i] = temp;
            char *temp = population[j];
            population[j] = population[i];
            population[i] = temp;
        }
    }
    // swap pivotpoint into position
}
void qsortParallelLists(char **population, int pop_size, int fitnesses[], int low, int high) {
    if (high > low) {
        int pivot = partition(population, pop_size, fitnesses, low, high);
        qsortParallelLists(population, pop_size, fitnesses, low, pivot-1);
        qsortParallelLists(population, pop_size, fitnesses, pivot+1, high);
    }
}
 */

int main(int argc, char *argv[]) { // call this program with */*.cnf
    SAT_problem prob;
    clock_t start, end;
    int file_index = 1;
    FILE *results; // final experiment stuff
    results = fopen("results.csv", "a");
    fprintf(results, "file,DPLL output,DPLL time (s),WalkSAT output,WalkSAT time (s),genetic output, genetic time (s)\n");
    while (file_index < argc) {
        prob = readInFile(argv[file_index]);
        printf("%s:\n", argv[file_index]);
        fprintf(results, "%s,", argv[file_index]);
        for (int i=0; i<3; i++) {
            switch (i) {
                case 0: // DPLL
                    printf("Begin DPLL:\n");
                    start = clock();
                    fprintf(results, "%d,", DPLLSAT(prob));
                    end = clock();
                    printf("-----------------------------\n");
                    fprintf(results, "%f,", ((double) (end - start)) / CLOCKS_PER_SEC);
                    break;
                case 1: // WalkSAT
                    printf("Begin WalkSAT:\n");
                    start = clock();
                    fprintf(results, "%d,", WalkSAT(prob, 0.2, 10000));
                    end = clock();
                    printf("-----------------------------\n");
                    fprintf(results, "%f,", ((double) (end - start)) / CLOCKS_PER_SEC);
                    break;
                case 2: // Genetic
                    printf("Begin GeneticSAT:\n");
                    start = clock();
                    fprintf(results, "%d,", geneticSAT(prob, 200, 10000));
                    end = clock();
                    printf("-----------------------------\n\n");
                    fprintf(results, "%f\n", ((double) (end - start)) / CLOCKS_PER_SEC);
                    break;
                default:
                    printf("Something's wrong!\n");
                    break;
            }
        }
        for (int i=0; i<prob.num_clauses; i++) {
            free(prob.clauses[i]);
        }
        free(prob.clauses);
        file_index++;
    }
    fclose(results);

    // testing
    //prob = readInFile("CBS/CBS_k3_n100_m403_b10_999.cnf");
    //printf("%d\n", WalkSAT(prob, 0.2, 10000));
    //printclauses(prob);
    //prob = readInFile(S_CNF_FILE);
    /* printf("%d\n", DPLLSAT(prob));
    printf("%d\n", WalkSAT(prob, 0.2, 10000));
    printf("%d\n", geneticSAT(prob, 300, 10000)); */
    /* for (int i=0; i<prob.num_clauses; i++) {
        free(prob.clauses[i]);
    }
    free(prob.clauses); */

    /* FILE *results;
    results = fopen("results.csv","a");
    fprintf(results, "file,DPLL output,DPLL time (s)\n");
    //fprintf(results, "file,trial,WalkSAT output,WalkSAT time (s),genetic output, genetic time (s)\n");
    while (file_index < argc) {
        prob = readInFile(argv[file_index]);
        printf("%s:\n", argv[file_index]);
        //for (int i=0; i<10; i++) {
            //fprintf(results, "%s,%d,", argv[file_index], i+1);
            fprintf(results, "%s,", argv[file_index]);
            printf("Begin DPLL:\n");
            start = clock();
            fprintf(results, "%d,", DPLLSAT(prob));
            end = clock();
            printf("-----------------------------\n");
            fprintf(results, "%f,", ((double) (end - start)) / CLOCKS_PER_SEC);
        //}
        for (int i=0; i<prob.num_clauses; i++) {
            free(prob.clauses[i]);
        }
        free(prob.clauses);
        file_index++;
    }
    fclose(results); */

    // doing 10 trials per random strategy
    /* FILE *results;
    results = fopen("results.csv","a");
    //fprintf(results, "file,WalkSAT output,WalkSAT time (s)\n");
    //fprintf(results, "file,trial,WalkSAT output,WalkSAT time (s),genetic output, genetic time (s)\n");
    while (file_index < argc) {
        prob = readInFile(argv[file_index]);
        printf("%s:\n", argv[file_index]);
        //for (int i=0; i<10; i++) {
            //fprintf(results, "%s,%d,", argv[file_index], i+1);
            fprintf(results, "%s,", argv[file_index]);
            printf("Begin WalkSAT:\n");
            start = clock();
            fprintf(results, "%d,", WalkSAT(prob, 0.2, 10000));
            end = clock();
            printf("-----------------------------\n");
            fprintf(results, "%f,", ((double) (end - start)) / CLOCKS_PER_SEC);
            printf("Begin GeneticSAT:\n");
            start = clock();
            fprintf(results, "%d,", geneticSAT(prob, 200, 10000));
            end = clock();
            printf("-----------------------------\n\n");
            fprintf(results, "%f\n", ((double) (end - start)) / CLOCKS_PER_SEC);
        //}
        for (int i=0; i<prob.num_clauses; i++) {
            free(prob.clauses[i]);
        }
        free(prob.clauses);
        file_index++;
    }
    fclose(results); */

    return 0;
}