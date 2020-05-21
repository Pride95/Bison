#include <config.h>
#include "system.h"
#include <stdio.h>

#include <bitset.h>
#include "state.h"
#include "state.h"
#include "symtab.h"
#include "ambiguity.h"
#include "conflicts.h"
#include "InadequacyList.h"
#include "gram.h"


reverse_transition **reverse_table;
a_state *sr_automata;


static void allocate_rever_table(void){
  reverse_table = xcalloc(nstates, sizeof(reverse_transition *));
  for(int i = 0; i < nstates; i++){
    reverse_table[i] =  xcalloc(nsyms, sizeof(reverse_transition));
  }
}


void static reverse_visit(rule *r, int *position, int start_state, int current_state){
  if(*position < 0){
    // ho finito creo il collegamento
    a_transition * tra = xcalloc(1, sizeof(a_transition));
    tra->epsilon = true;
    tra->red = r->number;
    tra->sym = r->lhs->number;
    int n_tr = states[current_state]->transitions->num;
    for(int i = 0; i < n_tr; i++){
      if(states[current_state]->transitions->states[i]->accessing_symbol == tra->sym){
        //ci siamo
        tra->number = states[current_state]->transitions->states[i]->number;
        a_state *start = &sr_automata[start_state];
        //start->transations
        start->transations = realloc(start->transations, sizeof(a_transition*)*start->num_transation+1);
        start->transations[start->num_transation] = tra;
        start->num_transation++;
        start->epsilon_trans = true;
      }
    }
    
    return;
  }
  int sym = *position;
  reverse_transition * r_tra = &reverse_table[current_state][sym];
  for(int i = 0; i < r_tra->num; i++){
    reverse_visit(r, position-1, start_state, r_tra->number[i]);
  }
}


static void build_sr_automata(void){
  sr_automata = xcalloc(nstates, sizeof(a_state));
  for (int i = 0; i < nstates; i++){
    sr_automata[i].number = states[i]->number;
    sr_automata[i].accessing_symbol = states[i]->accessing_symbol;
    sr_automata[i].reductions = states[i]->reductions;
    sr_automata[i].conflict = !states[i]->consistent;
    
    if(sr_automata[i].accessing_symbol == 0 && i != 0){
      //sono lo stato finale
      sr_automata[i].final = true;
    }
    
    int trans_number = 0;
    transitions *trans = states[i]->transitions;
    for(int j=0; j < trans->num; j++){
      if(TRANSITION_IS_SHIFT(trans, j) && !TRANSITION_IS_DISABLED(trans, j)){
        trans_number++;
      }
    }
    sr_automata[i].num_transation = trans_number;
    sr_automata[i].transations = xcalloc(trans_number, sizeof(a_transition*));
    trans_number = 0;
    for(int j=0; j < trans->num; j++){
      if(!TRANSITION_IS_DISABLED(trans, j)){
        symbol_number s = trans->states[j]->accessing_symbol;
        state_number t = trans->states[j]->number;
        if(TRANSITION_IS_SHIFT(trans, j)){
          a_transition * tra = xcalloc(1, sizeof(a_transition));
          tra->epsilon = false;
          tra->red = 0;
          tra->sym = s;
          tra->number = t;
          
          sr_automata[i].transations[trans_number] = tra;
          trans_number++;
        }
        reverse_transition * r_tra = &reverse_table[t][s];
        if(r_tra->num == 0){
          r_tra->number = xcalloc(1, sizeof(state_number));
          r_tra->number[0] = i;
          r_tra->num = 1;
        }
        else{
          r_tra->num++;
          r_tra->number = realloc(r_tra->number, sizeof(state_number)*r_tra->num);
          r_tra->number[r_tra->num-1] = i;
        }
      }
    }
  }
  
  
  for (int i = 0; i < nstates; i++){
    int num_red = sr_automata[i].reductions->num;
    if(num_red != 0){
      for(int j = 0; j < num_red; j++){
        int *k = sr_automata[i].reductions->rules[j]->rhs;
        while(*k > 0){
          if(*(k+1) < 0){
            break;
          }
          k++;
        }
        //fprintf (stderr, "ciao %d %d\n", *k, i);
        //for(int rh = 0)
        reverse_visit(sr_automata[i].reductions->rules[j], k, i, i);
      }
    }
  }
}


antagonist *antagonist1;
antagonist *antagonist2;
antagonist *intersection;

enumerate_auto *conf_automa;


void epsilon_closure(bitset b){
  for(int i = 0; i < nstates; i++){
    if(bitset_test(b, i) && sr_automata[i].epsilon_trans){
      a_state *a_s = &sr_automata[i];
      for(int j = 0; j< a_s->num_transation; j++){
        if(a_s->transations[j]->epsilon){
          bitset_set(b, a_s->transations[j]->number);
        }
      }
    }
  }
}


antagonist * construct_antagonist (int action, int position, a_state *s){
  antagonist *ant = xcalloc(1, sizeof(antagonist));
  ant->tipo_conflitto = action;
  if(action == 1){
    ant->num_state = 1;
    ant->stati = xcalloc(1, sizeof(sc_state *));
    ant->stati[0] = xcalloc(1, sizeof(sc_state));
    ant->stati[0]->state_set = bitset_create(nstates, BITSET_FIXED);
    rule_number num = s->reductions->rules[position]->number;
    ant->rule = num;
    for(int i = 0; i < s->num_transation; i++){
      if(s->transations[i]->epsilon && s->transations[i]->red == num){
        // sono al posto giusto
        bitset_set(ant->stati[0]->state_set, s->transations[i]->number);
      }
    }
    epsilon_closure(ant->stati[0]->state_set);
  }
  else if(action == 0){
    ant->num_state = 2;
    ant->stati = xcalloc(2, sizeof(sc_state *));
    ant->stati[0] = xcalloc(1, sizeof(sc_state));
    ant->stati[0]->state_set = bitset_create(nstates, BITSET_FIXED);
    ant->stati[0]->fake = true;
    
    ant->stati[0]->num_transation = 1;
    ant->stati[0]->transations = xcalloc(1, sizeof(a_transition*));
    a_transition *new_tran = xcalloc(1, sizeof(a_transition));
    new_tran->sym = s->transations[position]->sym;
    new_tran->number = 1;
    ant->stati[0]->transations[0] = new_tran;
    
    ant->stati[1] = xcalloc(1, sizeof(sc_state));
    ant->stati[1]->state_set = bitset_create(nstates, BITSET_FIXED);
    ant->sym = s->transations[position]->sym;
    bitset_set(ant->stati[1]->state_set, s->transations[position]->number);
    epsilon_closure(ant->stati[1]->state_set);
  }
  return ant;
}


void print_bitset_state(bitset b){
  for(int i = 0; i < nstates; i++){
    if(bitset_test(b, i)){
      fprintf(stderr, " %d - ", i);
    }
  }
  fprintf(stderr, "\n");
}


int state_exist(antagonist *a, bitset b){
  for(int i = 0; i < a->num_state; i++){
    if(bitset_equal_p(a->stati[i]->state_set, b) && !a->stati[i]->fake){
      return i;
    }
  }
  return -1;
}


void subset_costruction(antagonist *a, int s){
  sc_state *current = a->stati[s];
  epsilon_closure(current->state_set);
  // fprintf(stderr, " inizio subset per stato - %d \n", s);
  bitset new_bit = bitset_create(nstates, BITSET_FIXED);
  for(int i = 0; i < ntokens; i++){
    //per ogni simbolo token cerco una transizione
    bitset_zero(new_bit);
    
    bool final = false;
    for(int j = 0; j < nstates; j++){
      if(bitset_test(current->state_set, j)){
        a_state *next = &sr_automata[j];
        // fprintf(stderr, " %d - ", j);
        for(int tr = 0; tr < next->num_transation; tr++){
          if(next->transations[tr]->sym == i){
            bitset_set(new_bit, next->transations[tr]->number);
            if(sr_automata[next->transations[tr]->number].final){
              final = true;
            }
          }
        }
      }
    }
    // fprintf(stderr, " \n ");
    if(bitset_empty_p(new_bit)){
      continue;
    }
    epsilon_closure(new_bit);
    
    // ho finito le transizioni
    // cerco un altro stato uguale
    int exist = state_exist(a, new_bit);
    
    
    if(exist == -1){
      //fprintf(stderr, " new state - \n ");
      //print_bitset_state(new_bit);
     // fprintf(stderr, " -------------- \n ");
      // devo creare lo stato
      sc_state *new_state = xcalloc(1, sizeof(sc_state));
      new_state->state_set = bitset_create(nstates, BITSET_FIXED);
      new_state->final = final;
      //new_state->state_set
      bitset_copy(new_state->state_set, new_bit);
      //a->stati 
      a->stati = realloc(a->stati, sizeof(sc_state*)*a->num_state+1);
      a->stati[a->num_state] = new_state;
      a->num_state++;
      exist = a->num_state-1;
    }
    
    if(exist >= 0){
      // lo stato esiste gia e quindi devo solo collegarlo
      a_transition *new_tran = xcalloc(1, sizeof(a_transition));
      // e qui mettere i dati dentro la transizione magari
      new_tran->number = exist;
      new_tran->sym = i;
      if(current->num_transation == 0){
        current->transations = xcalloc(1, sizeof(a_transition*));
        current->num_transation = 1;
        current->transations[0] = new_tran;
      }
      else{
        current->transations = realloc(current->transations, sizeof(a_transition*)*current->num_transation+1);
        current->transations[current->num_transation] = new_tran;
        current->num_transation++;
      }
    }else{
      //non è possibile
    }
  }
  // fprintf(stderr, "numero di stati %d - \n ", a->num_state);
/*
  if(s <= a->num_state - 1){
    fprintf(stderr, " s alla fine ciclo %d - \n ", s);
    subset_costruction(a, s+1);
  }
*/
}


void complete_antagonist(antagonist* a){
  int i = 0;
  if(a->tipo_conflitto == 0){
    i = 1;
  }
  while(i < a->num_state){
    //fprintf(stderr, "numero di stati %d - \n ", a->num_state);
    //fprintf(stderr, "elaborazione per stato  %d - \n ", i);
    subset_costruction(a, i);
    if(i % 50 == 0){
      printf("elaborati %d stati\n", i);
    }
    i++;
  }
}


void print_bitset_state_inter(bitset b){
  for(int i = 0; i < antagonist1->num_state + antagonist2->num_state; i++){
    if(bitset_test(b, i)){
      fprintf(stderr, " %d - ", i);
    }
  }
  fprintf(stderr, "\n");
}


void elaborate_state_intersection(int s){
  sc_state *c = intersection->stati[s];
  int size_bitset = antagonist1->num_state + antagonist2->num_state;
  sc_state *ant1;
  sc_state *ant2;
  for(int i = 0; i < size_bitset; i++){
    if(bitset_test(c->state_set, i)){
      if(i >= antagonist1->num_state){
        ant2 = antagonist2->stati[i - antagonist1->num_state];
      }
      else{
        ant1 = antagonist1->stati[i];
      }
    }
  }
  
  for(int i = 0; i < ant1->num_transation; i++){
    int sym = ant1->transations[i]->sym;
    
    for(int j = 0; j < ant2->num_transation; j++){
      if(ant2->transations[j]->sym == sym){
        //abbiamo un match possiamo fare la transizione
        bitset new_bit = bitset_create(size_bitset, BITSET_FIXED);
        bitset_set(new_bit, ant1->transations[i]->number);
        bitset_set(new_bit, ant2->transations[j]->number + antagonist1->num_state);
        
        int exist = state_exist(intersection, new_bit);
        if(exist == -1){
          
          sc_state *new_state = xcalloc(1, sizeof(sc_state));
          new_state->state_set = bitset_create(size_bitset, BITSET_FIXED);
          //new_state->state_set
          bitset_copy(new_state->state_set, new_bit);
          //a->stati 
          intersection->stati = realloc(intersection->stati, 
                  sizeof(sc_state*)*intersection->num_state+1);
          intersection->stati[intersection->num_state] = new_state;
          intersection->num_state++;
          if(antagonist1->stati[ant1->transations[i]->number]->final || antagonist2->stati[ant2->transations[j]->number]->final){
            new_state->final = true;
          }
          exist = intersection->num_state-1;
        }
        if(exist >= 0){
          a_transition *new_tran = xcalloc(1, sizeof(a_transition));
          // e qui mettere i dati dentro la transizione magari
          new_tran->number = exist;
          new_tran->sym = sym;
          if(c->num_transation == 0){
            c->transations = xcalloc(1, sizeof(a_transition*));
            c->num_transation = 1;
            c->transations[0] = new_tran;
          }
          else{
            c->transations = realloc(c->transations, sizeof(a_transition*)*c->num_transation+1);
            c->transations[c->num_transation] = new_tran;
            c->num_transation++;
          }
        }
      }
    }
  }
}


void build_intersection(void){
  intersection = xcalloc(1, sizeof(antagonist));
  intersection->num_state = 1;
  intersection->stati = xcalloc(1, sizeof(sc_state *));
  intersection->stati[0] = xcalloc(1, sizeof(sc_state));
  //inizializzazione stato iniziale 
  int size_bitset = antagonist1->num_state + antagonist2->num_state;
  intersection->stati[0]->state_set = bitset_create(size_bitset, BITSET_FIXED);
  bitset_set(intersection->stati[0]->state_set, 0);
  bitset_set(intersection->stati[0]->state_set, antagonist1->num_state);
  int i = 0;
  while(i < intersection->num_state){
    elaborate_state_intersection(i);
    i++;
  }
}


bool check_intersection_empty(void){
  for(int i = 0; i < intersection->num_state; i++){
    if(intersection->stati[i]->final){
      return false;
    }
  }
  return true;
}


int max_len = 25;

int *word;
int *pre_word;
int len_word = 0;
int len_pre_word = 0;
int current_state = 0;
int current_symbol = 0;

bitset simboli_comflitto;


int *stack_stati;
int *stack_simboli;

int pos_stati;
int pos_simboli;

int len_stati;
int len_simboli;


void check_stacks(void){
  if(pos_stati >= len_stati){
    //ingrandisco gli stacks
    len_stati = len_stati + 10;
    len_simboli = len_simboli + 10;
    
    stack_stati = realloc(stack_stati, sizeof(int)*len_stati);
    stack_simboli = realloc(stack_simboli, sizeof(int)*len_simboli);
  }
}


int parse_word(int ant){
  //inizializzazione
  
  pos_simboli = 0;
  pos_stati = 0;
  
  len_stati = 10;
  len_simboli = 10;
  
  
  stack_simboli = xcalloc(len_simboli, sizeof(int));
  stack_stati = xcalloc(len_stati, sizeof(int));
  
  
  
  //symbols[0] = $end
  //symbols[ntokens] = $accept
  
  stack_stati[pos_stati] = 0;
  stack_simboli[pos_simboli] = 0;
  //pos_simboli++;
  //pos_stati++;
  
  
  int i = 0;
  while(i < len_pre_word){
    int st = stack_stati[pos_stati];
    int sym = pre_word[i];
    if(sym == -1){
      // è epsilon
      i++;
      continue;
    }
    state * s = states[st];
    bool shift = false;
    for(int j = 0; j < s->transitions->num; j++){
      if(s->transitions->states[j]->accessing_symbol == sym){
        //poso fare la transizione
        bool can_shift = false;
        if(sr_automata[st].conflict){
          for(int i = 0; i < conf_automa[st].num_conf; i++){
            if(conf_automa[st].c[i].sym == sym && conf_automa[st].c[i].operation == 0){
              //allora so cosa devo fare
              can_shift = true;
            }
          }
        }
        else{
          can_shift = true;
        }
        if(can_shift){
          pos_stati++;
          pos_simboli++;
          check_stacks();
          stack_simboli[pos_simboli] = sym;
          stack_stati[pos_stati] = s->transitions->states[j]->number;
          shift = true;
          break;
        }
      }
    }
    
    if(shift){
      i++;
      continue;
    }
    
    // controllo le riduzioni
    bool red = false;
    for(int j = 0; j < s->reductions->num; j++){
      bool pass_check = false;
      if(s->reductions->num == 1 && s->reductions->lookahead_tokens == NULL){
        //qualsiasi va bene per ridurre
        pass_check = true;
      }
      else{
        if(bitset_test(s->reductions->lookahead_tokens[j], sym)){
          pass_check = true;
        }
      }
      if(pass_check){
        //posso ridurre yea
        if(s->reductions->rules[j]->number == 0){
          //sto riducendo per la regola 0 quindi accetto 
          return 1;
        }
        int rul_num = s->reductions->rules[j]->number;
        bool can_reduce = true;
        if(sr_automata[st].conflict){
          for(int i = 0; i < conf_automa[st].num_conf; i++){
            if(conf_automa[st].c[i].sym == sym){
              if(!(conf_automa[st].c[i].operation == 1 && conf_automa[st].c[i].reduction == rul_num)){
                can_reduce = false;
              }
            }
          }
        }
        
        if(can_reduce){
          int shift_lhs = s->reductions->rules[j]->lhs->number;

          //faccio il pop dei simboli e dei stati
          int size_rhs = (int)rule_rhs_length(s->reductions->rules[j]);

          pos_simboli -= size_rhs;
          pos_stati -= size_rhs;
          //fatto il pop
          state * ss = states[stack_stati[pos_stati]];
          //lo stato da cui faro il goto

          for(int k = 0; k < ss->transitions->num; k++){
            if(ss->transitions->states[k]->accessing_symbol == shift_lhs){
              pos_simboli++;
              pos_stati++;
              check_stacks();
              stack_simboli[pos_simboli] = shift_lhs;
              stack_stati[pos_stati] = ss->transitions->states[k]->number;
              red = true;
            }
          }

          break;
        }
      }
    }
    if(red){
      continue;
    }
    // non ho shiftato e nemmeno ridotto per cui sono in errore
    return -1;
  }
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  i = 0;
  while(i < len_word){
    int st = stack_stati[pos_stati];
    int sym = word[i];
    if(sym == -1){
      // è epsilon
      i++;
      continue;
    }
    state * s = states[st];
    bool shift = false;
    for(int j = 0; j < s->transitions->num; j++){
      if(s->transitions->states[j]->accessing_symbol == sym){
        //poso fare la transizione
        bool can_shift = false;
        if(sr_automata[st].conflict){
          for(int i = 0; i < conf_automa[st].num_conf; i++){
            if(conf_automa[st].c[i].sym == sym && conf_automa[st].c[i].operation == 0){
              //allora so cosa devo fare
              can_shift = true;
            }
          }
        }
        else{
          can_shift = true;
        }
        if(can_shift){
          pos_stati++;
          pos_simboli++;
          check_stacks();
          stack_simboli[pos_simboli] = sym;
          stack_stati[pos_stati] = s->transitions->states[j]->number;
          shift = true;
          break;
        }
      }
    }
    
    if(shift){
      i++;
      continue;
    }
    
    // controllo le riduzioni
    bool red = false;
    for(int j = 0; j < s->reductions->num; j++){
      bool pass_check = false;
      if(s->reductions->num == 1 && s->reductions->lookahead_tokens == NULL){
        //qualsiasi va bene per ridurre
        pass_check = true;
      }
      else{
        if(bitset_test(s->reductions->lookahead_tokens[j], sym)){
          pass_check = true;
        }
      }
      if(pass_check){
        //posso ridurre yea
        if(s->reductions->rules[j]->number == 0){
          //sto riducendo per la regola 0 quindi accetto 
          return 1;
        }
        int rul_num = s->reductions->rules[j]->number;
        bool can_reduce = true;
        if(sr_automata[st].conflict){
          for(int i = 0; i < conf_automa[st].num_conf; i++){
            
            if(conf_automa[st].c[i].sym == sym){
              if(!(conf_automa[st].c[i].operation == 1 && conf_automa[st].c[i].reduction == rul_num)){
                can_reduce = false;
              }
            }
          }
        }
        
        if(can_reduce){
          int shift_lhs = s->reductions->rules[j]->lhs->number;

          //faccio il pop dei simboli e dei stati
          int size_rhs = (int)rule_rhs_length(s->reductions->rules[j]);

          pos_simboli -= size_rhs;
          pos_stati -= size_rhs;
          //fatto il pop
          state * ss = states[stack_stati[pos_stati]];
          //lo stato da cui faro il goto

          for(int k = 0; k < ss->transitions->num; k++){
            if(ss->transitions->states[k]->accessing_symbol == shift_lhs){
              pos_simboli++;
              pos_stati++;
              check_stacks();
              stack_simboli[pos_simboli] = shift_lhs;
              stack_stati[pos_stati] = ss->transitions->states[k]->number;
              red = true;
            }
          }

          break;
        }
      }
    }
    if(red){
      continue;
    }
    return -1;
  }
  
  if(stack_simboli[pos_simboli] == 0){
    //ho letto $end e l'ho anche messo e ho finito l'input
    return 1;
  }
  return -1;
}


void clean_stacks(){
  free(stack_stati);
  free(stack_simboli);
}


int check_word(void){
  
  // qui devo mettere i due stack uno per i simboli uno per i stati.
  
  int pos_conf = 0;
  
  if(current_symbol == -1){
    for(int j = 0; j < nsyms; j++){
      if(bitset_test(simboli_comflitto, j)){
        //devo settare
        for(int i = 0; i < sr_automata[current_state].num_conlicts; i++){
          if(sr_automata[current_state].conclicts[i]->sym == j){
            pos_conf = i;
          }
        }
        //controllo per antagonista 1
        conf_automa[current_state].c[pos_conf].sym = j;
        conf_automa[current_state].c[pos_conf].operation = antagonist1->tipo_conflitto;
        if(antagonist1->tipo_conflitto == 1){
          conf_automa[current_state].c[pos_conf].reduction = antagonist1->rule;
        }
      }
    }
  }
  else{
    for(int i = 0; i < sr_automata[current_state].num_conlicts; i++){
      if(sr_automata[current_state].conclicts[i]->sym == current_symbol){
        pos_conf = i;
      }
    }
    //controllo per antagonista 1
    conf_automa[current_state].c[pos_conf].sym = current_symbol;
    conf_automa[current_state].c[pos_conf].operation = antagonist1->tipo_conflitto;
    if(antagonist1->tipo_conflitto == 1){
      conf_automa[current_state].c[pos_conf].reduction = antagonist1->rule;
    }
  }
  
  int result1 = parse_word(1);
  
  
  
  
  //controllo per antagonista 2
  if(current_symbol == -1){
    for(int j = 0; j < nsyms; j++){
      if(bitset_test(simboli_comflitto, j)){
        //devo settare
        for(int i = 0; i < sr_automata[current_state].num_conlicts; i++){
          if(sr_automata[current_state].conclicts[i]->sym == j){
            pos_conf = i;
          }
        }
        //controllo per antagonista 1
        conf_automa[current_state].c[pos_conf].sym = j;
        conf_automa[current_state].c[pos_conf].operation = antagonist2->tipo_conflitto;
        if(antagonist1->tipo_conflitto == 1){
          conf_automa[current_state].c[pos_conf].reduction = antagonist2->rule;
        }
      }
    }
  }
  else{
    for(int i = 0; i < sr_automata[current_state].num_conlicts; i++){
      if(sr_automata[current_state].conclicts[i]->sym == current_symbol){
        pos_conf = i;
      }
    }
    //controllo per antagonista 1
    conf_automa[current_state].c[pos_conf].sym = current_symbol;
    conf_automa[current_state].c[pos_conf].operation = antagonist2->tipo_conflitto;
    if(antagonist1->tipo_conflitto == 1){
      conf_automa[current_state].c[pos_conf].reduction = antagonist2->rule;
    }
  }
  
  int result2 = parse_word(2);
  
  clean_stacks();
  
  if(result1 == 1 && result2 == 1){
    return 1;
  }
  
  return -1;
}


int create_pre_word(int p){
  if(len_pre_word > max_len){
    return -1;
  }
  a_state *s = &sr_automata[p];
  if(p == current_state){
    // sono allo stato dove comincia la subset-construction, quindi termino
    fprintf(stderr, "PRE parola da testare: ");
    for(int i = 0; i < len_pre_word; i++){
      if(pre_word[i] < 0){
        fprintf(stderr, "eps - ");
      }
      else{
        fprintf(stderr, "%s - ", symbols[pre_word[i]]->tag);
      }
    }
    fprintf(stderr, " / / %d\n", len_pre_word);
    int result = check_word();
    return result;
  }
  
  if(len_pre_word == 0){
    pre_word = calloc(1, sizeof(int));
  }
  
  // check per l'epsilon prima di allocare nuovo spazio
  // anzi no, me ne frego, lo skippo a parsing teoricamente
  
  len_pre_word++;
  pre_word = realloc(pre_word, sizeof(int)*len_pre_word);
  
  for(int i = 0; i < s->num_transation; i++){
    if(s->transations[i]->epsilon){
      pre_word[len_pre_word-1] = -1;
    }
    else{
      pre_word[len_pre_word-1] = s->transations[i]->sym;
    }
    int success = create_pre_word(s->transations[i]->number);
    if(success > 0){
      // len_pre_word--;
      return success;
    }
  }
  len_pre_word--;
  return -1;
}


int config_atutoma(int s, int sym){
  int result = -1;
  if(!(s < nstates)){
    result = create_pre_word(0);
    return result;
  }
  if(!sr_automata[s].conflict){
    result = config_atutoma(s+1, 0);
    return result;
  }
  
  a_state *c = &sr_automata[s];
  
  if(sym >= c->num_conlicts){
    result = config_atutoma(s+1, 0);
    return result;
  }
  
  conflict_sym *curr = c->conclicts[sym];
  
  //c->conclicts[sym]
  for(int i = 0; i < curr->num_conflicts; i++){
    
    if(curr->sym == current_symbol && s == current_state && current_symbol != -1){
      result = config_atutoma(s, sym+1);
    }
    else if(current_symbol == -1 && bitset_test(simboli_comflitto, curr->sym)){
      result = config_atutoma(s, sym+1);
    }
    else{
      conf_automa[s].c[sym].sym = curr->sym;
      conf_automa[s].c[sym].operation = curr->list_conflict[i].operation;
      conf_automa[s].c[sym].reduction = curr->list_conflict[i].reduction;
      conf_automa[s].c[sym].transition = curr->list_conflict[i].transition;
      result = config_atutoma(s, sym+1);
    }
    
    
    if(result == 1){
      return result;
    }
  }
  return result;
}


int next_symbol(int p){
  if(len_word > max_len){
    return -1;
  }
  sc_state *s = intersection->stati[p];
  if(s->final){
    // sono allo stato finale e di solito non ho transizioni quindi posso termianare
    fprintf(stderr, "Parola da testare: ");
    for(int i = 0; i < len_word; i++){
      fprintf(stderr, "%s - ", symbols[word[i]]->tag);
    }
    fprintf(stderr, "\n");
    int result = config_atutoma(0, 0);
    return result;
  }
  
  if(len_word == 0){
    word = calloc(1, sizeof(int));
  }
  len_word++;
  word = realloc(word, sizeof(int)*len_word);
  
  for(int i = 0; i < s->num_transation; i++){
    word[len_word-1] = s->transations[i]->sym;
    int success = next_symbol(s->transations[i]->number);
    if(success > 0){
      // len_word--;
      return success;
    }
  }
  len_word--;
  return -1;
}


int find_word(void){
  int success = next_symbol(0);
  return success;
}


void print_ambiguity(void){
  fprintf (stderr, "Ambiguita trovata, i due antagonisti sono: \n");
  fprintf (stderr, "antagonista 1: \n");
  if(antagonist1->tipo_conflitto == 0){
    fprintf (stderr, "dallo stato %d, shift per il symbolo %s \n", current_state, symbols[antagonist1->sym]->tag);
  }
  else{
    fprintf (stderr, "dallo stato %d, reduce per la regola %d \n", current_state, antagonist1->rule);
  }
  
  fprintf (stderr, "antagonista 2: \n");
  if(antagonist2->tipo_conflitto == 0){
    fprintf (stderr, "dallo stato %d, shift per il symbolo %s \n", current_state, symbols[antagonist2->sym]->tag);
  }
  else{
    fprintf (stderr, "dallo stato %d, reduce per la regola %d \n", current_state, antagonist2->rule);
  }
  
  fprintf (stderr, "prefisso della parola: \n");
  
  
  for(int i = 0; i < len_pre_word; i++){
    if(pre_word[i] < 0){
      //fprintf(stderr, "eps - ");
    }
    else{
      fprintf(stderr, "%s - ", symbols[pre_word[i]]->tag);
    }
  }
  fprintf(stderr, "\n");
  
  
  fprintf (stderr, "parola dell'intersezione: \n");
   for(int i = 0; i < len_word; i++){
    fprintf(stderr, "%s - ", symbols[word[i]]->tag);
  }
  fprintf(stderr, "\n");
  
  fprintf(stderr, "Configurazione automa");
  
  for(int i = 0; i < nstates; i++){
    fprintf(stderr, "Conf stato %d \n", i);  
    for(int j = 0; j < conf_automa[i].num_conf; j++){
      fprintf(stderr, "symbol - %s - ", symbols[conf_automa[i].c[j].sym]->tag);
      fprintf(stderr, " action %d , red: %d --- trans: %d \n ----- \n", conf_automa[i].c[j].operation, conf_automa[i].c[j].reduction, conf_automa[i].c[j].transition);
    }
  }
  fflush(stderr);
}


void free_automata(void){
  for(int i = 0; i < antagonist1->num_state; i++){
    bitset_free(antagonist1->stati[i]->state_set);
    for(int j = 0; j < antagonist1->stati[i]->num_transation; j++){
      free(antagonist1->stati[i]->transations[j]);
    }
    free(antagonist1->stati[i]->transations);
    free(antagonist1->stati[i]);
  }
  free(antagonist1->stati);
  free(antagonist1);
  antagonist1 = NULL;
  
  for(int i = 0; i < antagonist2->num_state; i++){
    bitset_free(antagonist2->stati[i]->state_set);
    for(int j = 0; j < antagonist2->stati[i]->num_transation; j++){
      free(antagonist2->stati[i]->transations[j]);
    }
    free(antagonist2->stati[i]->transations);
    free(antagonist2->stati[i]);
  }
  free(antagonist2->stati);
  free(antagonist2);
  antagonist2 = NULL;
  
  for(int i = 0; i < intersection->num_state; i++){
    bitset_free(intersection->stati[i]->state_set);
    for(int j = 0; j < intersection->stati[i]->num_transation; j++){
      free(intersection->stati[i]->transations[j]);
    }
    free(intersection->stati[i]->transations);
    free(intersection->stati[i]);
  }
  free(intersection->stati);
  free(intersection);
  intersection = NULL;
}


void set_ambiguity(void){
  for(int i = 0; i < nstates; i++){
    a_state *s = &sr_automata[i];
    if(!s->conflict){
      continue;
    }
    int num_red = s->reductions->num;
    bitset intersezione = bitset_create(ntokens, BITSET_FIXED);
    for(int i = 0; i < num_red; i++){
      // prima controllo gli altri reduce
      for(int j = 0; j < num_red; j++){
        bitset_zero(intersezione);
        if(j != i){
          bitset_intersection(intersezione, s->reductions->lookahead_tokens[j], 
                  s->reductions->lookahead_tokens[i]);
          int resl = bitset_count(intersezione);
          if(!bitset_empty_p(intersezione)){
            fprintf (stderr, "conflitto per la riduzione %d e la riduzione %d %d\n", i, j, resl);
            for(int k = 0; k < ntokens; k++){
              //states[5]->reductions->lookahead_tokens[0]
              if(bitset_test(intersezione, k)){
                int conf_posi = -1;
                for(int c = 0; c < s->num_conlicts; c++){
                  if(s->conclicts[c]->sym == k){
                    conf_posi = c;
                    break;
                  }
                }
                
                if(conf_posi == -1){
                  //non ho trovato lo aggiungo
                  if(s->num_conlicts == 0){
                    //creo
                    s->num_conlicts = 1;
                    s->conclicts = xcalloc(1, sizeof(conflict_sym *));
                  }
                  else{
                    s->num_conlicts++;
                    s->conclicts = realloc(s->conclicts, sizeof(conflict_sym *)*s->num_conlicts);
                  }
                  conflict_sym *new_conf = xcalloc(1, sizeof(conflict_sym));
                  new_conf->sym = k;
                  new_conf->num_conflicts = 2;
                  new_conf->list_conflict = xcalloc(new_conf->num_conflicts, sizeof(a_conflict));
                  
                  new_conf->list_conflict[0].operation = 1;
                  new_conf->list_conflict[1].operation = 1;
                  
                  new_conf->list_conflict[0].reduction = s->reductions->rules[i]->number;
                  new_conf->list_conflict[1].reduction = s->reductions->rules[j]->number;
                  
                  s->conclicts[s->num_conlicts - 1] = new_conf;
                }
                else{
                  //devo cercarlo magari c'è gia
                  conflict_sym *curr = s->conclicts[conf_posi];
                  bool red1_pres = false;
                  bool red2_pres = false;
                  for(int c = 0; c < curr->num_conflicts; c++){
                    if(curr->list_conflict[c].operation == 1 && 
                            curr->list_conflict[c].reduction == s->reductions->rules[i]->number){
                      red1_pres = true;
                    }
                    if(curr->list_conflict[c].operation == 1 && 
                            curr->list_conflict[c].reduction == s->reductions->rules[j]->number){
                      red2_pres = true;
                    }
                  }
                  if(!red1_pres){
                    curr->num_conflicts++;
                    curr->list_conflict = realloc(curr->list_conflict, sizeof(a_conflict)*curr->num_conflicts);
                    curr->list_conflict[curr->num_conflicts-1].operation = 1;
                    curr->list_conflict[curr->num_conflicts-1].reduction = s->reductions->rules[i]->number;
                  }
                  if(!red2_pres){
                    curr->num_conflicts++;
                    curr->list_conflict = realloc(curr->list_conflict, sizeof(a_conflict)*curr->num_conflicts);
                    curr->list_conflict[curr->num_conflicts-1].operation = 1;
                    curr->list_conflict[curr->num_conflicts-1].reduction = s->reductions->rules[j]->number;
                  }
                }
              }
            }
          }
        }
      }
      //poi controllo i shift
      int num_tran = s->num_transation;
      for(int j = 0; j < num_tran; j++){
        symbol_number sym_tra = s->transations[j]->sym;
        if(bitset_test(s->reductions->lookahead_tokens[i], sym_tra)){
          fprintf (stderr, "conflitto per la riduzione %d e e simbolo %d \n", i, sym_tra);
          int conf_posi = -1;
          for(int c = 0; c < s->num_conlicts; c++){
            if(s->conclicts[c]->sym == sym_tra){
              conf_posi = c;
              break;
            }
          }
          if(conf_posi == -1){
            //non ho trovato lo aggiungo
            if(s->num_conlicts == 0){
              //creo
              s->num_conlicts = 1;
              s->conclicts = xcalloc(1, sizeof(conflict_sym *));
            }
            else{
              s->num_conlicts++;
              s->conclicts = realloc(s->conclicts, sizeof(conflict_sym *)*s->num_conlicts);
            }
            conflict_sym *new_conf = xcalloc(1, sizeof(conflict_sym));
            new_conf->sym = sym_tra;
            new_conf->num_conflicts = 2;
            new_conf->list_conflict = xcalloc(new_conf->num_conflicts, sizeof(a_conflict));
            
            new_conf->list_conflict[0].operation = 1;
            new_conf->list_conflict[1].operation = 0;
            
            new_conf->list_conflict[0].reduction = s->reductions->rules[i]->number;
            new_conf->list_conflict[1].transition = s->transations[j]->sym;
            
            s->conclicts[s->num_conlicts - 1] = new_conf;
          }
          else{
            //devo cercarlo magari c'è gia
            conflict_sym *curr = s->conclicts[conf_posi];
            bool red1_pres = false;
            bool shift2_pres = false;
            for(int c = 0; c < curr->num_conflicts; c++){
              if(curr->list_conflict[c].operation == 1 && curr->list_conflict[c].reduction == s->reductions->rules[i]->number){
                red1_pres = true;
              }
              if(curr->list_conflict[c].operation == 2 && curr->list_conflict[c].transition == s->transations[j]->sym){
                shift2_pres = true;
              }
            }
            if(!red1_pres){
              curr->num_conflicts++;
              curr->list_conflict = realloc(curr->list_conflict, sizeof(a_conflict)*curr->num_conflicts);
              curr->list_conflict[curr->num_conflicts-1].operation = 1;
              curr->list_conflict[curr->num_conflicts-1].transition = s->reductions->rules[i]->number;
            }
            if(!shift2_pres){
              curr->num_conflicts++;
              curr->list_conflict = realloc(curr->list_conflict, sizeof(a_conflict)*curr->num_conflicts);
              curr->list_conflict[curr->num_conflicts-1].operation = 1;
              curr->list_conflict[curr->num_conflicts-1].transition = s->transations[j]->sym;
            }
          }
        }
      }
    }
    bitset_free(intersezione);
  }
}


void allocate_enumeration_automata(void){
  conf_automa = xcalloc(nstates, sizeof(enumerate_auto));
  for(int i = 0; i < nstates; i++){
    if(!sr_automata[i].conflict){
      continue;
    }
    conf_automa[i].num_conf = sr_automata[i].num_conlicts;
    conf_automa[i].c = xcalloc(conf_automa[i].num_conf, sizeof(a_enum_conf));
  }
}


int ambiguity_state (int stato){
  a_state *s = &sr_automata[stato];
  int num_red = s->reductions->num;
  bitset intersezione = bitset_create(ntokens, BITSET_FIXED);
  simboli_comflitto = bitset_create(ntokens, BITSET_FIXED);
  for(int i = 0; i < num_red; i++){
    // prima controllo gli altri reduce
    for(int j = 0; j < num_red; j++){
      bitset_zero(intersezione);
      if(j != i){
        
        bitset_intersection(intersezione, s->reductions->lookahead_tokens[j], 
               s->reductions->lookahead_tokens[i]);
        
        if(!bitset_empty_p(intersezione)){
          fprintf (stderr, "conflitto per la riduzione %d e la riduzione %d su vari simboli possibilmente\n", i, j);
          
          bitset_copy(simboli_comflitto, intersezione);
          antagonist1 = construct_antagonist(1, i, s); //reduce
          antagonist2 = construct_antagonist(1, j, s); //reduce
          complete_antagonist(antagonist1);
          complete_antagonist(antagonist2);
          current_state = s->number;
          current_symbol = -1;
          
          build_intersection();
          int result = 0;
          if(!check_intersection_empty()){
            result = find_word(); 
          }

          if(result == 1){
            print_ambiguity();
            
            bitset_free(intersezione);
            bitset_free(simboli_comflitto);
            free_automata();
            return result;
          }
          free_automata();
        }
        
        /*for(int k = 0; k < nsyms; k++){
          if(bitset_test(s->reductions->lookahead_tokens[j], k) && 
                  bitset_test(s->reductions->lookahead_tokens[i], k)){
            fprintf (stderr, "conflitto per la riduzione %d e la riduzione %d sul simbolo %s\n", i, j, symbols[k]->tag);
            
            
            antagonist1 = construct_antagonist(1, i, s); //reduce
            antagonist2 = construct_antagonist(1, j, s); //reduce
            complete_antagonist(antagonist1);
            complete_antagonist(antagonist2);
            current_state = s->number;
            current_symbol = k;
            build_intersection();
            int result = 0;
            if(!check_intersection_empty()){
              result = find_word(); 
            }

            if(result == 1){
              print_ambiguity();
              bitset_free(intersezione);
              free_automata();
              return result;
            }
            free_automata();
          }
          
        }*/
      }
    }
    //poi controllo i shift
    int num_tran = s->num_transation;
    for(int j = 0; j < num_tran; j++){
      symbol_number sym_tra = s->transations[j]->sym;
      if(bitset_test(s->reductions->lookahead_tokens[i], sym_tra)){
        fprintf (stderr, "conflitto per la riduzione %d e e simbolo %d \n", i, sym_tra);
        printf("inizio costruzione antagonista 1\n");
        antagonist1 = construct_antagonist(1, i, s); //reduce
        printf("inizio costruzione antagonista 2\n");
        antagonist2 = construct_antagonist(0, j, s); //shift
        
        printf("inizio subset antagonista 1\n");
        
        complete_antagonist(antagonist1);
        
        printf("inizio subset antagonista 2\n");
        
        complete_antagonist(antagonist2);
        
        printf("finito subset\n");
        current_state = s->number;
        current_symbol = sym_tra;
        printf("inizio costruzione intersezione\n");
        build_intersection();
        int result = 0;
        if(!check_intersection_empty()){
          printf("inizio generazione parole\n");
          result = find_word(); 
        }
        
        if(result == 1){
          print_ambiguity();
          bitset_free(intersezione);
          free_automata();
          return result;
        }
        free_automata();
      }
    }
  }
  bitset_free(simboli_comflitto);
  bitset_free(intersezione);
  printf("finiti gli stati \n");
}


int ambiguity(void){
  int result = 0;
  for(int i = 0; i< nstates; i++){
    if(sr_automata[i].conflict){
      fprintf (stderr, "conflitto nello stato %d %d\n", i, sr_automata[i].conflict);
      result = ambiguity_state(i);
      if(result == 1){
        return result;
      }
    }
  }
}


void print_sr_automata(void){
  for(int i = 0; i < nstates; i++){
    a_state *c = &sr_automata[i];
    fprintf(stderr, "State %d:\n", c->number);
    fprintf(stderr, "Symbol %d:\n", c->accessing_symbol);
    fprintf(stderr, "Transitions:\n");
    for(int j = 0; j < c->num_transation; j++){
      fprintf(stderr, "\t %s -> %d\n", symbols[c->transations[j]->sym]->tag, c->transations[j]->number );
    }
    fprintf(stderr, "--------\n\n");
  }
}


void check_ambiguity(void){
  setbuf(stdout, NULL);
  setbuf(stderr, NULL);
  fprintf(stdout, "inizio ambiguita, fprintf \n");
  printf("inizio ambiguita printf \n");
  fflush(stdout);
  
  allocate_rever_table();
  build_sr_automata();
  //print_sr_automata();
  set_ambiguity();
  allocate_enumeration_automata();
  ambiguity();
}
