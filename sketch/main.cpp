#include "viterbi.h"

#include <cinttypes>
#include <cmath>
#include <cstdlib>
#include <cstring>

#include <chrono>

void fail(const char *tyname) {
  fprintf(stderr, "Error: expected %s\n", tyname);
  exit(1);
}

double read_f32(FILE *fp) {
  float v;
  if (fscanf(fp, "%f", &v) != 1) {
    fail("f32");
  }
  return v;
}

int64_t read_i64(FILE *fp) {
  int64_t v;
  if (fscanf(fp, "%" SCNd64, &v) != 1) {
    fail("i64");
  }
  return v;
}

uint16_t read_u16(FILE *fp) {
  uint16_t v;
  if (fscanf(fp, "%" SCNu16, &v) != 1) {
    fail("u16");
  }
  return v;
}

uint8_t read_u8(FILE *fp) {
  uint8_t v;
  if (fscanf(fp, "%" SCNu8, &v) != 1) {
    fail("u8");
  }
  return v;
}

void read_f32_1d(futhark_context *ctx, futhark_f32_1d **a, char *file) {
  FILE *fp = fopen(file, "r");
  int64_t d0 = read_i64(fp);
  float *data = (float*)malloc(d0 * sizeof(float));
  for (int i = 0; i < d0; i++) {
    data[i] = read_f32(fp);
  }
  *a = futhark_new_f32_1d(ctx, data, d0);
  free(data);
}

void read_f32_2d(futhark_context *ctx, futhark_f32_2d **a, char *file) {
  FILE *fp = fopen(file, "r");
  int64_t d0 = read_i64(fp);
  int64_t d1 = read_i64(fp);
  float *data = (float*)malloc(d0 * d1 * sizeof(float));
  for (int i = 0; i < d0; i++) {
    for (int j = 0; j < d1; j++) {
      data[i*d1+j] = read_f32(fp);
    }
  }
  *a = futhark_new_f32_2d(ctx, data, d0, d1);
  free(data);
}

void read_u16_2d(futhark_context *ctx, futhark_u16_2d **a, char *file) {
  FILE *fp = fopen(file, "r");
  int64_t d0 = read_i64(fp);
  int64_t d1 = read_i64(fp);
  uint16_t *data = (uint16_t*)malloc(d0 * d1 * sizeof(uint16_t));
  for (int i = 0; i < d0; i++) {
    for (int j = 0; j < d1; j++) {
      data[i*d1+j] = read_u16(fp);
    }
  }
  *a = futhark_new_u16_2d(ctx, data, d0, d1);
  free(data);
}

void read_input_signals_2d(futhark_context *ctx, futhark_u8_2d **a, int64_t **lens, char *file) {
  FILE *fp = fopen(file, "r");
  int64_t d0 = read_i64(fp);
  int64_t d1 = read_i64(fp);
  int64_t *n = (int64_t*)malloc(d0 * sizeof(int64_t));
  for (int i = 0; i < d0; i++) {
    n[i] = read_i64(fp);
  }
  *lens = n;
  uint8_t *data = (uint8_t*)malloc(d0 * d1 * sizeof(uint8_t));
  for (int i = 0; i < d0; i++) {
    for (int j = 0; j < d1; j++) {
      data[i*d1+j] = read_u8(fp);
    }
  }
  *a = futhark_new_u8_2d(ctx, data, d0, d1);
  free(data);
}

void read_f32_0d(double *v, char *file) {
  FILE *fp = fopen(file, "r");
  *v = read_f32(fp);
}

int main(int argc, char **argv) {
  futhark_context_config *config = futhark_context_config_new();
  futhark_context *ctx = futhark_context_new(config);

  futhark_f32_2d *output_prob = nullptr;
  futhark_f32_2d *initial_prob = nullptr;
  futhark_f32_2d *trans1 = nullptr;
  futhark_f32_1d *trans2 = nullptr;
  double gamma = NAN;
  futhark_u8_2d *input_signals = nullptr;
  int64_t *input_signal_lens = nullptr;
  futhark_u16_2d *predecessors = nullptr;
  int i = 1;
  while (i < argc) {
    if (strcmp(argv[i], "--output-prob") == 0) {
      read_f32_2d(ctx, &output_prob, argv[i+1]);
    } else if (strcmp(argv[i], "--initial-prob") == 0) {
      read_f32_2d(ctx, &initial_prob, argv[i+1]);
    } else if (strcmp(argv[i], "--trans1") == 0) {
      read_f32_2d(ctx, &trans1, argv[i+1]);
    } else if (strcmp(argv[i], "--trans2") == 0) {
      read_f32_1d(ctx, &trans2, argv[i+1]);
    } else if (strcmp(argv[i], "--gamma") == 0) {
      read_f32_0d(&gamma, argv[i+1]);
    } else if (strcmp(argv[i], "--input-signals") == 0) {
      read_input_signals_2d(ctx, &input_signals, &input_signal_lens, argv[i+1]);
    } else if (strcmp(argv[i], "--predecessors") == 0) {
      read_u16_2d(ctx, &predecessors, argv[i+1]);
    } else {
      printf("Error: unknown flag %s\n", argv[i]);
      exit(1);
    }
    i += 2;
  }
  if (output_prob == nullptr || initial_prob == nullptr || trans1 == nullptr ||
      trans2 == nullptr || std::isnan(gamma) || input_signals == nullptr ||
      predecessors == nullptr) {
    fprintf(stderr, "Not all required arguments were specified\n");
    exit(1);
  }

  auto start = std::chrono::steady_clock::now();

#ifdef FORWARD_ALG
  futhark_f32_1d *out;
  int res = futhark_entry_forward(ctx, &out, gamma, trans1, trans2, output_prob, initial_prob, predecessors, input_signals);
#else
  futhark_u16_2d *out;
  int res = futhark_entry_viterbi(ctx, &out, gamma, trans1, trans2, output_prob, initial_prob, predecessors, input_signals);
#endif
  if (res != FUTHARK_SUCCESS) {
    printf("Futhark call failed: %s\n", futhark_context_get_error(ctx));
    exit(1);
  }
  res = futhark_context_sync(ctx);
  if (res != FUTHARK_SUCCESS) {
    printf("Futhark context sync failed: %s\n", futhark_context_get_error(ctx));
    exit(1);
  }
  futhark_free_f32_2d(ctx, output_prob);
  futhark_free_f32_2d(ctx, initial_prob);
  futhark_free_f32_2d(ctx, trans1);
  futhark_free_f32_1d(ctx, trans2);
  futhark_free_u16_2d(ctx, predecessors);
  futhark_free_u8_2d(ctx, input_signals);

#ifdef FORWARD_ALG
  free(input_signal_lens);
  const int64_t *shape = futhark_shape_f32_1d(ctx, out);
  float *probs = (float*)malloc(shape[0] * sizeof(float));
  futhark_values_f32_1d(ctx, out, probs);
  for (int i = 0; i < shape[0]; i++) {
    printf("%lf ", probs[i]);
  }
  printf("\n");
  free(probs);
  futhark_free_f32_1d(ctx, out);
#else
  const int64_t *shape = futhark_shape_u16_2d(ctx, out);
  uint16_t *data = (uint16_t*)malloc(shape[0] * shape[1] * sizeof(uint16_t));
  futhark_values_u16_2d(ctx, out, data);
  char outc[4] = {'A', 'C', 'G', 'T'};
  for (int i = 0; i < shape[0]; i++) {
    printf("signal #%d\n", i+1);
    for (int j = 0; j < input_signal_lens[i]; j++) {
      if ((data[i*shape[1]+j] & 15) == 0) {
        int val = (data[i*shape[1]+j] >> 4) & 3;
        printf("%c", outc[val]);
      }
    }
    printf("\n");
  }
  free(data);
  free(input_signal_lens);
  futhark_free_u16_2d(ctx, out);
#endif

  int t = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now()-start).count();
  fprintf(stderr, "Futhark execution took %d ms\n", t);

  futhark_context_free(ctx);
  futhark_context_config_free(config);

  return 0;
}
