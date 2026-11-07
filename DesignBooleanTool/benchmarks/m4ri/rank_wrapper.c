#include <stdint.h>
#include <string.h>
#include <m4ri/m4ri.h>
#ifdef _WIN32
#define API __declspec(dllexport)
#else
#define API
#endif
API int db_m4ri_rank(int nrows,int ncols,const uint8_t *raw,int stride){
 if(nrows<0||ncols<0||stride<(ncols+7)/8)return -1;
 if(!nrows||!ncols)return 0;
 mzd_t *A=mzd_init(nrows,ncols);
 for(int i=0;i<nrows;i++){
   memcpy(mzd_row(A,i),raw+(size_t)i*stride,(ncols+7)/8);
   if(ncols%64)mzd_row(A,i)[A->width-1]&=(((uint64_t)1<<(ncols%64))-1);
 }
 int rank=mzd_echelonize(A,0);
 mzd_free(A);return rank;
}
