#version 450

void main() {
    float x = 3.0f;
    float y = x + 0.5f;
    vec4 v = vec4(x, y, 1.0f, 0.0f);
    vec2 v2 = vec2(1.0, 1.0);
    vec4 v3 = vec4(v2, 0.3f, 0.2f);
    v3.yx = v.xx;
    v3.w = 1.0f;
}