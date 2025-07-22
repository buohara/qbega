#include <stdio.h>

main()
{
    float a = 3.14;
    float b = 10.26;

    float c = a + b;
    float d = a - b;
    float e = a * b;
    float f = b / a;

    int g   = 3;
    float h = a + g;
    float i = a - g;
    float j = a * g;
    float k = a / g;

    printf("%3.2f\n", c);
    printf("%3.2f\n", d);
    printf("%3.2f\n", d);
    printf("%3.2f\n", f);
    printf("%3.2f\n", g);
    printf("%3.2f\n", h);
    printf("%3.2f\n", i);
    printf("%3.2f\n", j);
}