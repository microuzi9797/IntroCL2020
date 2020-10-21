#include <stdio.h>

typedef struct pigeonhole
{
    unsigned int pigeon_index;
    unsigned int hole_index;
    unsigned int atom_index;
}Pigeonhole;

unsigned int combinations(unsigned int n, unsigned int k);

int main()
{
    //inputs
    unsigned int n, m;
    scanf("%u %u", &n, &m);
    //nbvar
    unsigned int nbvar = n * m;
    Pigeonhole p[n][m];
    for (unsigned int i = 0; i < n; i++)
    {
        for (unsigned int j = 0; j < m; j++)
        {
            p[i][j].pigeon_index = i + 1;
            p[i][j].hole_index = j + 1;
            p[i][j].atom_index = i * m + j + 1;
        }
    }
    //nbclause
    unsigned int nbclause = n + combinations(n, 2) * m;
    //outputs
    FILE *fp;
    fp = fopen("output.cnf", "w");
    fprintf(fp, "c\n");
    fprintf(fp, "c start with comments\n");
    fprintf(fp, "c\n");
    fprintf(fp, "c the pigeonhole problem with %u pigeons and %u holes\n", n, m);
    fprintf(fp, "c\n");
    fprintf(fp, "c pigeon_index = ((atom_index - 1) / m) + 1 \n");
    fprintf(fp, "c hole_index = atom_index mod m\n");
    fprintf(fp, "c\n");
    fprintf(fp, "c\n");
    fprintf(fp, "p cnf %u %u\n", nbvar, nbclause);
    for (unsigned int i = 0; i < n; i++)
    {
        for (unsigned int j = 0; j < m; j++)
        {
            fprintf(fp, "%u ", p[i][j].atom_index);
        }
        fprintf(fp, "0\n");
    }
    for (unsigned int i = 0; i < m; i++)
    {
        for (unsigned int j = 0; j < n; j++)
        {
            for (unsigned int k = j + 1; k < n; k++)
            {
                fprintf(fp, "-%u -%u 0\n", p[j][i].atom_index, p[k][i].atom_index);
            }
        }
    }
    fclose(fp);
    return 0;
}

unsigned int combinations(unsigned int n, unsigned int k)
{
    unsigned int num1, num2, num3;
    num1 = 1;
    num2 = 1;
    num3 = 1;
    for (unsigned int i = 1; i <= n; i++)
    {
        num1 *= i;
    }
    for (unsigned int i = 1; i <= k; i++)
    {
        num2 *= i;
    }
    for (unsigned int i = 1; i <= (n - k); i++)
    {
        num3 *= i;
    }
    return (num1 / (num2 * num3));
}