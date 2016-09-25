#version 450

bool foo(uint x) {
    return x < 4;
}
void main() {
    uint cond = 3;
    if (foo(cond)) {
        uint x = 0;
        uint y = x+1;
    } else {
        uint a = 1;
        uint b = a*a;
    }
}