/* 
 * File:   ambiguity.h
 * Author: tesi
 *
 * Created on 14 aprile 2020, 22.24
 */

#ifndef AMBIGUITY_H
#define	AMBIGUITY_H

#include "gram.h"
#include <bitset.h>


typedef struct{
    bool epsilon;
    rule_number red;
    symbol_number sym;
    state_number number;
} a_transition;


typedef struct {
    int num;
    state_number *number;
} reverse_transition;


typedef struct {
    int operation;
    //0 - shift  //1 - reduce
    int transition;
    int reduction;
} a_conflict;


typedef struct {
    symbol_number sym;
    int num_conflicts;
    a_conflict *list_conflict;
} conflict_sym;


typedef struct {
    state_number number;
    symbol_number accessing_symbol;
    reductions *reductions;
    bool conflict;
    bool epsilon_trans;
    int num_transation;
    a_transition **transations;
    bool final;
    conflict_sym **conclicts;
    int num_conlicts;
} a_state;


typedef struct {
    bitset state_set;
    int num_transation;
    a_transition **transations;
    bool final;
    bool fake;
} sc_state;


typedef struct{
    sc_state **stati;
    int num_state;
    int tipo_conflitto;
    //0 - shift  //1 - reduce
    symbol_number sym;
    rule_number rule;
} antagonist;


typedef struct{
    symbol_number sym;
    int operation;
    //0 - shift  //1 - reduce
    int transition;
    int reduction;
} a_enum_conf;


typedef struct{
    int num_conf;
    a_enum_conf *c;
} enumerate_auto;


extern reverse_transition **reverse_table;
extern a_state *sr_automata;

void check_ambiguity(void);

#endif	/* AMBIGUITY_H */

