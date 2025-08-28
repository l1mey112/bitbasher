int square(int num) {
    return num * num;
}

unsigned popcount_naive(unsigned n) {
    unsigned c = 0;
    while (n) {
        c += n & 1;
        n >>= 1;
    }
    return c;
}
