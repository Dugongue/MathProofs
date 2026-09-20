#ifndef CYCLECOUNTER_H
#define CYCLECOUNTER_H

#include <stdint.h>

void enable_cyclecounter();

void disable_cyclecounter();

long long get_cyclecounter();

#endif