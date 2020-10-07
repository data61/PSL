#include <stdio.h>
#include <stdlib.h>

int main(int argc, const char *argv[])
{
	if (argc != 2) {
		fprintf(stderr, "Usage: %s numberOfPhis\n", argv[0]);
		return EXIT_FAILURE;
	}

	unsigned phis;
	if (sscanf(argv[1], "%u", &phis) != 1) {
		fprintf(stderr, "Cannot parse number of phis\n");
		return EXIT_FAILURE;
	}

	printf("int main(int argc, char *argv[])\n{\n");

	for (unsigned i = 0; i != phis; i++) {
		printf("\tif (argc) { }\n");
	}

	printf("\n\treturn 0;\n}\n");

	return EXIT_SUCCESS;
}
