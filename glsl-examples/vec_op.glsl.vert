#version 450

void main() {
    vec3 w = vec3(1.0, 0.3, 0.2);
    vec3 x = normalize(w);
    vec3 y = cross(x, x);
}