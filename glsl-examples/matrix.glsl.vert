#version 450

struct test { mat4 a; vec4 b; };

void main() {
    mat4 x;
    transpose(x);
    inverse(x);
    mat4 y = x + x;
    mat4 z = y - x;

    test struct_test;

    struct_test.a += x;
    struct_test.b += vec4(1.0);

    y += x;
    z += y;
}