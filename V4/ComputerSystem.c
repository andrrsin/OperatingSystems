#include <string.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include "ComputerSystem.h"
#include "OperatingSystem.h"
#include "ComputerSystemBase.h"
#include "Processor.h"
#include "Messages.h"
#include "Asserts.h"
#include "Wrappers.h"

//Import Heap
#include "Heap.h"

extern int COLOURED;
extern char *debugLevel;

//V3 arrivalTimeQueue
heapItem *arrivalTimeQueue;
int numberOfProgramsInArrivalTimeQueue=0;

// Functions prototypes
void ComputerSystem_PrintProgramList();

// Powers on of the Computer System.


void ComputerSystem_PowerOn(int argc, char *argv[], int paramIndex) {
	
	unsigned int i;
	// To remember the simulator sections to be message-debugged
	for (i=0; i< strlen(debugLevel);i++) {
	  if (isupper(debugLevel[i])){
		COLOURED = 1;
		debugLevel[i]=tolower(debugLevel[i]);
	  }
	}

	// Load debug messages
	int nm=0;
	nm=Messages_Load_Messages(nm,TEACHER_MESSAGES_FILE);
	if (nm<0) {
		ComputerSystem_DebugMessage(NO_TIMED_MESSAGE,64,SHUTDOWN,TEACHER_MESSAGES_FILE);
		exit(2);
	}
	nm=Messages_Load_Messages(nm,STUDENT_MESSAGES_FILE);

	// Prepare if necesary the assert system
	Asserts_LoadAsserts();
	
	ComputerSystem_DebugMessage(TIMED_MESSAGE, 99, POWERON, "STARTING simulation\n");
	// Obtain a list of programs in the command line
	
	int programsFromFilesBaseIndex = ComputerSystem_ObtainProgramList(argc, argv, paramIndex);

	//We create the arrivalTimeQueue with the number of total programs
	arrivalTimeQueue = Heap_create(programsFromFilesBaseIndex);
	
	ComputerSystem_PrintProgramList();
	// Request the OS to do the initial set of tasks. The last one will be
	// the processor allocation to the process with the highest priority
	OperatingSystem_Initialize(programsFromFilesBaseIndex);
	
	// Tell the processor to begin its instruction cycle 
	Processor_InstructionCycleLoop();
	
}

// Powers off the CS (the C program ends)
void ComputerSystem_PowerOff() {
	// Show message in red colour: "END of the simulation\n" 
	ComputerSystem_DebugMessage(TIMED_MESSAGE,99,SHUTDOWN,"END of the simulation\n"); 
	exit(0);
}

/////////////////////////////////////////////////////////
//  New functions below this line  //////////////////////


void ComputerSystem_PrintProgramList() {
	//programList //Can be called everywhere
	int i = 1;
	
	ComputerSystem_DebugMessage(NO_TIMED_MESSAGE, 101, INIT);
	
	while (programList[i] != NULL)
	{	
		
		
		ComputerSystem_DebugMessage(NO_TIMED_MESSAGE, 102, INIT, i,programList[i]->executableName,programList[i]->arrivalTime);
		i = i + 1;
	}
	

			
		
	
	
}
