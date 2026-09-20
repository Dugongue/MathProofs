#ifndef PROFILERESULT_H
#define PROFILERESULT_H

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#include "cyclecounter.h"

#define PROFILER_CYCLE_COST 159

typedef struct
{
  char name[256];
  long long total_cycle_count;
  long long start_cycle_count;
  long long cycle_counts[100];
  int cycle_count_index;
  int runs;
} profileresult;

extern profileresult profileresults[1000];
extern int number_of_profileresults;
extern int profiler_enabled;

static int compare_profileresults(const void *a, const void *b)
{
  return ((profileresult *)b)->total_cycle_count - ((profileresult *)a)->total_cycle_count;
}

static void complete_profiler()
{
  qsort(profileresults, number_of_profileresults, sizeof(profileresult), compare_profileresults);
}

static int compare(const void *a, const void *b)
{
  return (*(long long *)a - *(long long *)b);
}

static float median(long long arr[], int n)
{
  qsort(arr, n, sizeof(long long), compare);

  if (n % 2 != 0)
  {
    return arr[n / 2];
  }
  else
  {
    return (arr[n / 2 - 1] + arr[n / 2]) / 2.0;
  }
}

static float median_2(long long arr[], int measurements, int print)
{
  int n = measurements - 1;
  long long differences[n];
  if (print == 1)
  {
    printf("MEDIANS:\n");
  }
  for (int i = 0; i < n; i++)
  {
    differences[i] = arr[i + 1] - arr[i];
    if (print)
    {
      printf("%lld ", differences[i]);
    }
  }
  if (print == 1)
  {
    printf("\n");
  }
  qsort(differences, n, sizeof(long long), compare);
  if (n % 2 == 0)
    return (differences[n / 2 - 1] + differences[n / 2]) / 2.0;
  else
    return differences[n / 2];
}

static float standard_deviation(long long arr[], int n)
{
  float mean = 0;
  for (int i = 0; i < n; i++)
  {
    mean += arr[i];
  }
  mean /= n;

  float variance = 0;
  for (int i = 0; i < n; i++)
  {
    float diff = arr[i] - mean;
    if (diff < 0)
    {
      diff = -diff;
    }
    variance += diff;
  }
  variance /= n;

  return variance;
}

#if PROFILER

#include <stdio.h>
#include <string.h>

#define PROFILER_ENABLE()                   \
  do                                        \
  {                                         \
    fprintf(stderr, "Profiler: ENABLED\n"); \
    profiler_enabled = 1;                   \
  } while (0)

#define PROFILER_DISABLE() \
  do                       \
  {                        \
    profiler_enabled = 0;  \
  } while (0)

#define PROFILER_START(target_name)                                                    \
  do                                                                                   \
  {                                                                                    \
    if (profiler_enabled == 0)                                                         \
      break;                                                                           \
    int found = 0;                                                                     \
    for (int i = 0; i < number_of_profileresults; i++)                                 \
    {                                                                                  \
      if (strcmp(profileresults[i].name, target_name) == 0)                            \
      {                                                                                \
        found = 1;                                                                     \
        profileresults[i].start_cycle_count = get_cyclecounter();                      \
        break;                                                                         \
      }                                                                                \
    }                                                                                  \
    if (!found)                                                                        \
    {                                                                                  \
      strcpy(profileresults[number_of_profileresults].name, target_name);              \
      profileresults[number_of_profileresults].total_cycle_count = 0;                  \
      profileresults[number_of_profileresults].start_cycle_count = get_cyclecounter(); \
      number_of_profileresults++;                                                      \
      if (number_of_profileresults > 999)                                              \
      {                                                                                \
        fprintf(stderr, "Profiling exceeded maximum number of results\n");             \
        exit(-1);                                                                      \
      }                                                                                \
    }                                                                                  \
  } while (0)

#define PROFILER_STOP(target_name)                                                           \
  do                                                                                         \
  {                                                                                          \
    if (profiler_enabled == 0)                                                               \
      break;                                                                                 \
    long long end_cycle_count = get_cyclecounter();                                          \
    for (int i = 0; i < number_of_profileresults; i++)                                       \
    {                                                                                        \
      if (strcmp(profileresults[i].name, target_name) == 0)                                  \
      {                                                                                      \
        long long cycle_count = end_cycle_count - profileresults[i].start_cycle_count;       \
        cycle_count -= PROFILER_CYCLE_COST;                                                  \
        profileresults[i].total_cycle_count += cycle_count;                                  \
        profileresults[i].start_cycle_count = 0;                                             \
        if (profileresults[i].cycle_count_index < 100)                                       \
        {                                                                                    \
          profileresults[i].cycle_counts[profileresults[i].cycle_count_index] = cycle_count; \
          profileresults[i].cycle_count_index++;                                             \
        }                                                                                    \
        profileresults[i].runs++;                                                            \
        break;                                                                               \
      }                                                                                      \
    }                                                                                        \
  } while (0)

#else

#define PROFILER_ENABLE()                       \
  do                                            \
  {                                             \
    fprintf(stderr, "Profiler: NOT DEFINED\n"); \
  } while (0)
#define PROFILER_DISABLE() \
  do                       \
  {                        \
  } while (0)
#define PROFILER_START(target_name) \
  do                                \
  {                                 \
  } while (0)
#define PROFILER_STOP(target_name) \
  do                               \
  {                                \
  } while (0)

#endif

#endif
