

int additional_compute(int val) {
    return val;
}

void compute(int* ptr) {
    *ptr = additional_compute(*ptr);
}
