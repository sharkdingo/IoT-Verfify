// src/assets/config/deviceTemplates.ts
import type { DeviceTemplate } from '../../types/device'

export const defaultDeviceTemplates: DeviceTemplate[] = [
    {
        id: 'ac_cooler_tpl',
        name: 'AC_Cooler',
        manifest: {
            Name: 'AC Cooler',
            Description: 'remove heat to cool the air',
            InternalVariables: [],
            ImpactedVariables: ['temperature'],
            InitState: 'Working',
            WorkingStates: [
                {
                    Name: 'Off',
                    Dynamics: [{ VariableName: 'temperature', ChangeRate: '0' }],
                    Invariant: 'true',
                    Description: 'The equipment is closed',
                    Trust: 'trusted'
                },
                {
                    Name: 'Working',
                    Dynamics: [{ VariableName: 'temperature', ChangeRate: '-1' }],
                    Invariant: 'true',
                    Description: 'The equipment is working',
                    Trust: 'trusted'
                }
            ],
            APIs: [
                {
                    Name: 'Turn_On',
                    StartState: 'Off',
                    EndState: 'Working',
                    Signal: true,
                    Description: ''
                },
                {
                    Name: 'Turn_Off',
                    StartState: 'Working',
                    EndState: 'Off',
                    Signal: true,
                    Description: ''
                }
            ]
        }
    },
    {
        id: 'ac_heater_tpl',
        name: 'AC_Heater',
        manifest: {
            Name: 'AC Heater',
            Description: 'Heating',
            InternalVariables: [],
            ImpactedVariables: ['temperature'],
            InitState: 'Off',
            WorkingStates: [
                {
                    Name: 'Off',
                    Dynamics: [{ VariableName: 'temperature', ChangeRate: '0' }],
                    Invariant: 'true',
                    Description: 'The equipment is closed',
                    Trust: 'trusted'
                },
                {
                    Name: 'Working',
                    Dynamics: [{ VariableName: 'temperature', ChangeRate: '1' }],
                    Invariant: 'true',
                    Description: 'The equipment is working',
                    Trust: 'trusted'
                }
            ],
            APIs: [
                {
                    Name: 'Turn_On',
                    StartState: 'Off',
                    EndState: 'Working',
                    Signal: true,
                    Description: ''
                },
                {
                    Name: 'Turn_Off',
                    StartState: 'Working',
                    EndState: 'Off',
                    Signal: true,
                    Description: ''
                }
            ]
        }
    }
]
